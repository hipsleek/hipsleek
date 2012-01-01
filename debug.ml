open Globals

let debug_on = ref false
let devel_debug_on = ref false
let devel_debug_print_orig_conseq = ref false

let log_devel_debug = ref false
let debug_log = Buffer.create 5096

let clear_debug_log () = Buffer.clear debug_log
let get_debug_log () = Buffer.contents debug_log

(* debugging facility for user *)

(* used to enable the printing of the original consequent while devel debugging. By default, orig_conseq is disabled*)
let enable_dd_and_orig_conseq_printing () =
 devel_debug_on := true;
 devel_debug_print_orig_conseq :=  true

let string_of_pos (pos:loc) =
  pos.start_pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^ ": "^(string_of_int (pos.start_pos.Lexing.pos_cnum-pos.start_pos.Lexing.pos_bol))^": "

let print s = if !debug_on then (print_string ("\n\n!!!" ^ s); flush stdout) else ()

let pprint msg (pos:loc) = 
  let tmp = pos.start_pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^ ": "^ (string_of_int (pos.start_pos.Lexing.pos_cnum-pos.start_pos.Lexing.pos_bol))^ ": " ^ msg in
	print tmp

(* system development debugging *)
let ho_print (pr:'a->string) (m:'a) : unit = 
  let d = Gen.StackTrace.is_same_dd_get () in
  if !devel_debug_on  || not(d==None) then 
    let s = (pr m) in
    let msg = match d with 
      | None -> ("\n!!!" ^ s)
      | Some cid -> ("\n@"^(string_of_int cid)^"!"^ s) 
    in
    if !log_devel_debug then 
      Buffer.add_string debug_log msg
    else
      (print_string msg; flush stdout)
  else ()

(* system development debugging *)
let devel_print s = 
  ho_print (fun x -> x) s 
(* let d = Gen.StackTrace.is_same_dd_get () in *)
(*   if !devel_debug_on  || not(d==None) then  *)
(*     let msg = match d with  *)
(*       | None -> ("\n!!!" ^ s) *)
(*       | Some cid -> ("\n@"^(string_of_int cid)^"!"^ s)  *)
(*     in *)
(*     if !log_devel_debug then  *)
(*       Buffer.add_string debug_log msg *)
(*     else *)
(*       (print_string msg; flush stdout) *)
(*   else () *)

let prior_msg pos =
  let tmp = pos.start_pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^ ": " ^ (string_of_int (pos.start_pos.Lexing.pos_cnum-pos.start_pos.Lexing.pos_bol)) ^ ": " in
  let tmp = if is_no_pos !entail_pos then tmp 
  else (tmp^"[entail:"^(string_of_int !entail_pos.start_pos.Lexing.pos_lnum)^"]"^"[post:"^(string_of_int (post_pos#get).start_pos.Lexing.pos_lnum)^"]") 
  in tmp

let devel_pprint (msg:string) (pos:loc) =
	ho_print (fun m -> (prior_msg pos)^m) msg

let devel_zprint msg (pos:loc) =
	ho_print (fun m -> (prior_msg pos)^(Lazy.force m)) msg

let trace_pprint (msg:string) (pos:loc) : unit = 
	ho_print (fun a -> " "^a) msg


let trace_hprint (pr:'a->string) (m:'a) (pos:loc) = 
	ho_print (fun x -> " "^(pr x)) m

let trace_zprint m (pos:loc) = 
	ho_print (fun x -> Lazy.force x) m


(* let devel_zprint msg (pos:loc) = *)
(* 	lazy_print (prior_msg pos) msg *)

(* let trace_zprint msg (pos:loc) =  *)
(* 	lazy_print (fun () -> " ") msg *)


let print_info prefix str (pos:loc) = 
  let tmp = "\n" ^ prefix ^ ":" ^ pos.start_pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^": " ^ (string_of_int (pos.start_pos.Lexing.pos_cnum-pos.start_pos.Lexing.pos_bol)) ^": " ^ str ^ "\n" in
	print_string tmp; flush stdout
