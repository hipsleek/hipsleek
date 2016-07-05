(* open Globals *)
open Gen.Basic
open VarGen

let debug_on = ref false
let devel_debug_on = ref false
let devel_debug_print_orig_conseq = ref false
let trace_on = ref true

let z_debug_arg = ref (None:Str.regexp option)

let () = if !compete_mode then
  begin
    trace_on := false;
  end
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
let ho_print flag (pr:'a->string) (m:'a) : unit =
  let d = Gen.StackTrace.is_same_dd_get () in
  (* let () = print_endline ("\ndd_get:"^((pr_option string_of_int) d)) in *)
  (* WN : should we use && or || *)
  if !compete_mode then ()
  else if (flag (* !devel_debug_on *)  ||  not(d==None)) then 
    let s = (pr m) in
    let msg = match d with 
      | None -> ("\n!!!" ^ s)
      | Some cid -> ("\n@"^(string_of_int cid)^"!"^ s) 
    in
    (* if !log_devel_debug then  *)
    (*   Buffer.add_string debug_log msg *)
    (* else *)
      (print_string msg; flush stdout)
  else ()

(* system development debugging *)
let devel_print s = 
  ho_print !devel_debug_on (fun x -> x) s 
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
  let tmp = if is_no_pos !VarGen.entail_pos then tmp 
  else (tmp^"[entail:"^(string_of_int !VarGen.entail_pos.start_pos.Lexing.pos_lnum)^"]"^"[post:"^(string_of_int (VarGen.post_pos#get).start_pos.Lexing.pos_lnum)^"]") 
  in tmp

let devel_pprint (msg:string) (pos:loc) =
  let flag = !devel_debug_on in
  ho_print flag (fun m -> (prior_msg pos)^m) msg

let devel_hprint (pr:'a->string) (m:'a) (pos:loc) = 
  let flag = !devel_debug_on in
  ho_print flag (fun x -> (prior_msg pos)^(pr x)) m

let devel_zprint msg (pos:loc) =
  let flag = !devel_debug_on in
  ho_print flag (fun m -> (prior_msg pos)^(Lazy.force m)) msg

let catch_exc m f x = 
  try 
    f x
  with e -> (print_endline m; flush stdout; raise e)

let dinfo_zprint m p = devel_zprint m p
let dinfo_hprint pr m p  = devel_hprint pr m p
let dinfo_pprint m p = devel_pprint m p

let binfo_pprint (msg:string) (pos:loc) =
  let s = if !devel_debug_on then (prior_msg pos) else " " in
  let flag = !trace_on || !devel_debug_on in
  ho_print flag (fun m -> s^m) msg

let winfo_pprint (msg:string) (pos:loc) =
  let s = if !devel_debug_on then (prior_msg pos) else " " in
  let flag = !trace_on || !devel_debug_on in
  ho_print flag (fun m -> s^m) ("**WARNING**"^msg)

let binfo_hprint (pr:'a->string) (m:'a) (pos:loc) = 
  let s = if !devel_debug_on then (prior_msg pos) else " " in
  let flag = !trace_on || !devel_debug_on in
  ho_print flag (fun x -> s^(pr x)) m

let binfo_zprint msg (pos:loc) =
  let s = if !devel_debug_on then (prior_msg pos) else " " in
  let flag = !trace_on || !devel_debug_on in
  ho_print flag (fun m -> s^(Lazy.force m)) msg


let binfo_start (msg:string) =
        binfo_pprint "**********************************" no_pos;
        binfo_pprint ("**** "^msg^" ****") no_pos;
        binfo_pprint "**********************************" no_pos

let binfo_end (msg:string) =
        binfo_pprint "**********************************" no_pos;
        binfo_pprint ("**** end of "^msg^" ****") no_pos;
        binfo_pprint "**********************************" no_pos

let dinfo_start (msg:string) =
        dinfo_pprint "**********************************" no_pos;
        dinfo_pprint ("**** "^msg^" detected ****") no_pos;
        dinfo_pprint "**********************************" no_pos

let dinfo_end (msg:string) =
        dinfo_pprint "**********************************" no_pos;
        dinfo_pprint ("**** end of "^msg^" ****") no_pos;
        dinfo_pprint "**********************************" no_pos

let ninfo_zprint m p = ()
let ninfo_hprint pr m p  = ()
let ninfo_pprint m p = ()

(*
  -- -v:10-50 (for details + all tracing + omega)
  -- -v:1-9 (for details only)
  -- -v:50.. (for tracing only)
  -- -v:-1 (minimal tracing)
  -- -v:-2..(exact tracing)
*)

let add_str s f xs = s^":"^(f xs)

let gen_vv_flags d =
  let m = !VarGen.verbose_num in
  let (flag,str) =
    if d<0 then (m==d,"EXACT:")
    else if m>50 then (d>=m,"DEBUG:")
    else if m<10 then (m>=d,"")
    else if d>=50 then (true,"DEBUG_"^(string_of_int d)^":")
    else (m>=d,"") in
  (flag,str)

let verbose_hprint (d:int) (p:'a -> string) (arg:'a)  =
  let (flag,str)=gen_vv_flags d in
  ho_print flag (add_str str p) arg

(* let verbose_pprint (d:int) (msg:string)  = *)
(*   verbose_hprint d (fun m -> m) msg *)

(* let verbose_pprint (d:int) (msg)  = *)
(*   verbose_hprint d (fun m -> m) msg *)

let vv_pprint d msg = verbose_hprint d (fun m -> m) msg

let vv_hprint d f arg = verbose_hprint d f arg

let vv_zprint d lmsg = 
  verbose_hprint d (fun x -> Lazy.force x) lmsg

let vv_plist d ls = 
  let (flag,str) = gen_vv_flags d in
  let rec helper ls =
    match ls with
      | [] -> ()
      | ((m,y)::xs) ->
            begin
            (ho_print flag (fun msg -> str^m^":"^msg) y)
                ; helper xs
            end
  in helper ls

let vv_hdebug f arg = vv_hprint 200 f arg 

(* less tracing *)
let vv_pdebug msg = vv_hdebug (fun m -> m) msg

let vv_debug msg = vv_pdebug msg

(* detailed tracing *)
let vv_trace msg = vv_hprint 100 (fun m -> m) msg

let vv_zdebug msg = vv_hdebug (fun x -> Lazy.force x) msg

let vv_result (s:string) (d:int) ls =
  vv_pprint d (">>>>>>>>>"^s^">>>>>>>>>");
  vv_plist d ls;
  vv_pprint d (">>>>>>>>>"^s^">>>>>>>>>")

let trace_pprint (msg:string) (pos:loc) : unit = 
	ho_print !devel_debug_on (fun a -> " "^a) msg

let trace_hprint (pr:'a->string) (m:'a) (pos:loc) = 
	ho_print !devel_debug_on (fun x -> " "^(pr x)) m

let trace_zprint m (pos:loc) = 
	ho_print !devel_debug_on (fun x -> Lazy.force x) m

let tinfo_zprint m p = trace_zprint m p
let tinfo_hprint pr m p  = trace_hprint pr m p
let tinfo_pprint m p = trace_pprint m p

let info_pprint (msg:string) (pos:loc) : unit =
  let flag = not(!compete_mode) in
  ho_print flag (fun a -> " "^a) msg

let info_hprint (pr:'a->string) (m:'a) (pos:loc) = 
  let flag = not(!compete_mode) in
  ho_print flag (fun x -> " "^(pr x)) m

let info_ihprint (pr:'a->string) (m:'a) (pos:loc) =
  let flag = not(!compete_mode) in
  if !VarGen.sap then ho_print flag (fun x -> " "^(pr x)) m
  else ()

let info_zprint m (pos:loc) = 
  let flag = not(!compete_mode) in
  ho_print flag (fun x -> Lazy.force x) m

(* let devel_zprint msg (pos:loc) = *)
(* 	lazy_print (prior_msg pos) msg *)

(* let trace_zprint msg (pos:loc) =  *)
(* 	lazy_print (fun () -> " ") msg *)


let print_info prefix str (pos:loc) = 
  let tmp = "\n" ^ prefix ^ ":" ^ pos.start_pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^": " ^ (string_of_int (pos.start_pos.Lexing.pos_cnum-pos.start_pos.Lexing.pos_bol)) ^": " ^ str ^ "\n" in
	print_string tmp; flush stdout


open Gen.StackTrace
 
  (* let ho_2_opt_aux (loop_d:bool) (test:'z -> bool) (s:string) (pr1:'a->string) (pr2:'b->string) (pr_o:'z->string)  (f:'a -> 'b -> 'z)  *)
  (*       (e1:'a) (e2:'b) : 'z = *)
  (*   let s,h = push s in *)
  (*   (if loop_d then print_string (h^" inp :"^(pr1 e1)^"\n")); *)
  (*   let r = try *)
  (*     pop_ho (f e1) e2  *)
  (*   with ex ->  *)
  (*       let () = print_string (h^"\n") in *)
  (*       let () = print_string (s^" inp1 :"^(pr1 e1)^"\n") in *)
  (*       let () = print_string (s^" inp2 :"^(pr2 e2)^"\n") in *)
  (*       let () = print_string (s^" Exception"^(Printexc.to_string ex)^"Occurred!\n") in *)
  (*       raise ex in *)
  (*   if not(test r) then r else *)
  (*     let () = print_string (h^"\n") in *)
  (*     let () = print_string (s^" inp1 :"^(pr1 e1)^"\n") in *)
  (*     let () = print_string (s^" inp2 :"^(pr2 e2)^"\n") in *)
  (*     let () = print_string (s^" out :"^(pr_o r)^"\n") in *)
  (*     r *)

(* ss with at least one argument *)
let pick_front n ss =
  let rec aux n ss  =
    match ss with
      | [] -> ss
      | s::ss -> let m=String.length s in
        if n>=m then s::aux (n-m) ss 
        else []
  in match ss with 
    | [] -> ss
    | s::ss -> s::(aux (n-(String.length s)) ss)

(* module type LABEL_TYPE = *)
(*     sig *)
(*       type a *)
(*       type t  *)
(*       val unlabelled : t  *)
(*       val is_unlabelled : t -> bool (\* is this unlabelled *\) *)
(*       val norm : t -> t (\* sort a label *\) *)
(*       val is_compatible : t -> t -> bool *)
(*       val is_compatible_rec : t -> t -> bool *)
(*       (\* val comb_identical : t -> t -> t (\\* combine two identical labels *\\) *\) *)
(*       val comb_norm : int -> t -> t -> t (\* combine two normalised labels *\) *)
(*       val string_of : t -> string *)
(*       val compare : t -> t -> int *)
(*       val singleton : a -> t *)
(*       val convert : string -> lst_pair -> t *)
(*     end;; *)



module DebugCore  =
struct
  let ho_aux ?(arg_rgx=None) df lz (loop_d:bool) (test:'z -> bool) (g:('a->'z) option) (s:string) (args:string list) (pr_o:'z->string) (f:'a->'z) (e:'a) :'z =
    let pre_str = "(=="^(VarGen.last_posn # get_rm)^"==)" in
      (* if s=="" thenmatch s with  *)
      (*   | None -> "" *)
      (*   | Some s ->  *)
      (*         (\* let () = VarGen.last_posn := None in *\) *)
      (*         "("^s^")" in *)
    let pr_args xs =
      let rec helper (i:int) args = match args with
        | [] -> ()
        | a::args -> (print_string (s^" inp"^(string_of_int i)^" :"^a^"\n");(helper (i+1) args)) in
      helper 1 xs in
    let pr_lazy_res xs =
      let rec helper xs = match xs with
        | [] -> ()
        | (i,a)::xs -> let a1=Lazy.force a in
          if (a1=(List.nth args (i-1))) then helper xs
          else (print_string (s^" res"^(string_of_int i)^" :"^(a1)^"\n");(helper xs)) in
      helper xs in
    let check_args args = true
      (* match !z_debug_arg with *)
      (*   | None -> false  *)
      (*   | Some re ->  *)
      (*         (\* let () = print_endline ("check_args:"^s) in *\) *)
      (*         List.exists (fun x ->  *)
      (*             try  *)
      (*               (Str.search_forward re x 0);true *)
      (*             with _ -> false) args *)
    in
    let (test,pr_o) = match g with
      | None -> (test,pr_o)
      | Some g -> 
            let res = ref (None:(string option)) in
            let new_test z =
              (try
                let r = g e in
                let rs = pr_o r in              
                if String.compare (pr_o z) rs==0 then false
                else (res := Some rs; true)
              with ex ->  
                  (res := Some (" OLD COPY : EXIT Exception"^(Printexc.to_string ex)^"!\n");
                  true)) in
            let new_pr_o x = (match !res with
              | None -> pr_o x
              | Some s -> ("DIFFERENT RESULT from PREVIOUS METHOD"^
                    ("\n PREV :"^s)^
                    ("\n NOW :"^(pr_o x)))) in
            (new_test, new_pr_o) in
    let s,h = push_call_gen s df in
    let h = pre_str^"\n"^h in
    (if loop_d then print_string ("\n"^h^" ENTRY :"^(String.concat "  " (pick_front 80 args))^"\n"));
    flush stdout;
    let r = (try
      pop_aft_apply_with_exc f e
    with ex -> 
        (
        (* if not df then *) 
        let flag = check_args args in
        if flag then
          begin
            let () = print_string ("\n"^h^"\n") in
            (pr_args args; pr_lazy_res lz);
            let () = print_string (s^" EXIT Exception"^(Printexc.to_string ex)^"Occurred!\n") in
            flush stdout;
            raise ex 
          end
        else raise ex
        )) in
    (if not(test r) then r else
      (* if not df then *)
      let res_str = pr_o r in
      let flag = check_args (res_str::args) in
      if not(flag) then r
      else
        begin
          let () = print_string ("\n"^h^"\n") in
          (pr_args args; pr_lazy_res lz);
          let () = print_string (s^" EXIT:"^(res_str)^"\n") in
          flush stdout;
          r
        end
    )

let choose bs xs = 
  let rec hp bs xs = match bs,xs with
    |[], _ -> []
    | _, [] -> []
    | b::bs, (i,s)::xs -> if b then (i,s)::(hp bs xs) else (hp bs xs) in
  hp bs xs

let ho_aux_no (f:'a -> 'z) (last:'a) : 'z =
  push_no_call ();
  (* VarGen.last_posn # reset; *)
  pop_aft_apply_with_exc_no f last


let ho_1_opt_aux df (flags:bool list) (loop_d:bool) (test:'z -> bool) g (s:string) (pr1:'a->string) (pr_o:'z->string)  (f:'a -> 'z) (e1:'a) : 'z =
  let a1 = pr1 e1 in
  let lz = choose flags [(1,lazy (pr1 e1))] in
  let f  = f in
  ho_aux df lz loop_d test g s [a1] pr_o  f  e1


let ho_2_opt_aux df (flags:bool list) (loop_d:bool) (test:'z -> bool) g (s:string) (pr1:'a->string) (pr2:'b->string) (pr_o:'z->string)  (f:'a -> 'b -> 'z) 
      (e1:'a) (e2:'b) : 'z =
  let a1 = pr1 e1 in
  let a2 = pr2 e2 in
  let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2))] in
  let f  = f e1 in
  let g  = match g with None -> None | Some g -> Some (g e1) in
  ho_aux df lz loop_d test g s [a1;a2] pr_o f e2

let ho_3_opt_aux df  (flags:bool list) (loop_d:bool) (test:'z -> bool) g (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr_o:'z->string)  (f:'a -> 'b -> 'c -> 'z) (e1:'a) (e2:'b) (e3:'c) : 'z =
  let a1 = pr1 e1 in
  let a2 = pr2 e2 in
  let a3 = pr3 e3 in
  let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3))] in
  let f  = f e1 e2 in
  let g  = match g with None -> None | Some g -> Some (g e1 e2) in
  ho_aux df lz loop_d test g s [a1;a2;a3] pr_o f e3


let ho_4_opt_aux df (flags:bool list) (loop_d:bool) (test:'z->bool) g (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string) (pr_o:'z->string) 
      (f:'a -> 'b -> 'c -> 'd-> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d): 'z =
  let a1 = pr1 e1 in
  let a2 = pr2 e2 in
  let a3 = pr3 e3 in
  let a4 = pr4 e4 in
  let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3)); (4,lazy (pr4 e4))] in
  let f  = f e1 e2 e3 in
  let g  = match g with None -> None | Some g -> Some (g e1 e2 e3) in
  ho_aux df lz loop_d test g s [a1;a2;a3;a4] pr_o f e4


let ho_5_opt_aux df (flags:bool list) (loop_d:bool) (test:'z -> bool)  g (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string)
      (pr5:'e->string) (pr_o:'z->string) 
      (f:'a -> 'b -> 'c -> 'd -> 'e -> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d) (e5:'e) : 'z =
  let a1 = pr1 e1 in
  let a2 = pr2 e2 in
  let a3 = pr3 e3 in
  let a4 = pr4 e4 in
  let a5 = pr5 e5 in
  let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3)); (4,lazy (pr4 e4)); (5,lazy (pr5 e5))] in
  let f  = f e1 e2 e3 e4 in
  let g  = match g with None -> None | Some g -> Some (g e1 e2 e3 e4) in
  ho_aux df lz loop_d test g s [a1;a2;a3;a4;a5] pr_o f e5


let ho_6_opt_aux df (flags:bool list) (loop_d:bool) (test:'z->bool) g (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string)
      (pr5:'e->string) (pr6:'f->string) (pr_o:'z->string) 
      (f:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d) (e5:'e) (e6:'f): 'z =
  let a1 = pr1 e1 in
  let a2 = pr2 e2 in
  let a3 = pr3 e3 in
  let a4 = pr4 e4 in
  let a5 = pr5 e5 in
  let a6 = pr6 e6 in
  let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3)); (4,lazy (pr4 e4)); (5,lazy (pr5 e5)); (6,lazy (pr6 e6))] in
  let f  = f e1 e2 e3 e4 e5 in
  let g  = match g with None -> None | Some g -> Some (g e1 e2 e3 e4 e5) in
  ho_aux df lz loop_d test g s [a1;a2;a3;a4;a5;a6] pr_o f e6

let ho_7_opt_aux df (flags:bool list) (loop_d:bool) (test:'z->bool) g (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string)
      (pr5:'e->string) (pr6:'f->string) (pr7:'h->string) (pr_o:'z->string) 
      (f:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'h-> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d) (e5:'e) (e6:'f) (e7:'h): 'z =
  let a1 = pr1 e1 in
  let a2 = pr2 e2 in
  let a3 = pr3 e3 in
  let a4 = pr4 e4 in
  let a5 = pr5 e5 in
  let a6 = pr6 e6 in
  let a7 = pr7 e7 in
  let lz = choose flags [(1,lazy (pr1 e1)); (2,lazy (pr2 e2)); (3,lazy (pr3 e3)); (4,lazy (pr4 e4)); (5,lazy (pr5 e5)); (6,lazy (pr6 e6)); (7,lazy (pr7 e7))] in
  let f  = f e1 e2 e3 e4 e5 e6 in
  let g  = match g with None -> None | Some g -> Some (g e1 e2 e3 e4 e5 e6) in
  ho_aux df lz loop_d test g s [a1;a2;a3;a4;a5;a6;a7] pr_o f e7

(* better re-organization *)
(* f:output->bool, b_loop:bool *)
let ho_1_preopt f b_loop = ho_1_opt_aux false [] b_loop f None
let to_1_preopt f b_loop = ho_1_opt_aux true [] b_loop f None
let ho_1_pre b_loop = ho_1_preopt (fun _ -> true) b_loop
let to_1_pre b_loop = to_1_preopt (fun _ -> true) b_loop
let ho_1 s = ho_1_pre false s
let to_1 s = to_1_pre false s
let ho_1_opt f = ho_1_preopt f false
let ho_1_loop s = ho_1_pre true s 


type debug_option =
  | DO_None
  | DO_Trace
  | DO_Loop
  | DO_Both
  | DO_Normal

let debug_map = Hashtbl.create 50

let regexp_line = ref []
let regexp_line_str = ref []

let z_debug_file = ref ""
(* let z_debug_regexp = ref None *)
let mk_debug_arg s =
  let re = Str.regexp s in
  z_debug_arg := Some re

(*let debug_file = open_in_gen [Open_creat] 0o666 ("z-debug.log")*)
let debug_file ()=
  let get_path s = 
    if String.contains s '/' then
      let i = String.rindex s '/' in
      String.sub s 0 (i+1)
    else ""
  in
  let fname = !z_debug_file in
  (* print_endline ("Debug File : "^fname); *)
  let n = String.length fname in
  if n>1 && fname.[0]='$' then
    begin
      (* z_debug_regexp := Some fname; *)
      let re = String.sub fname 1 (n-1) in
      regexp_line_str := [re];
      None
    end
  else
    begin
      let debug_conf = "./" ^ fname in
      (* let () = print_endline (debug_conf) in *)
      let global_debug_conf =
        if (Sys.file_exists debug_conf) then
          debug_conf
        else (get_path Sys.executable_name) ^ (String.sub debug_conf 2 ((String.length debug_conf) -2))
      in
      (* let () = print_endline global_debug_conf in *)
      try
        Some(open_in (global_debug_conf))
      with _ ->
          begin
            print_endline_quiet ("WARNING : cannot find debug file "^fname); 
            z_debug_flag:=false;
            None
          end
    end

let read_from_debug_file chn : string list =
  let line = ref [] in
  (* let quitloop = ref false in *)
  (try
    while true do
      let xs = (input_line chn) in
      let xs = String.trim xs in
      let n = String.length xs in
      (* let s = String.sub xs 0 1 in *)
      if n > 0 && xs.[0]!='#' (* String.compare s "#" !=0 *) then begin
        line := xs::!line;
      end;
      if n > 1 && xs.[0]=='$' (* String.compare s "#" !=0 *) then begin
        let xs = String.sub xs 1 (n-1) in
        (* regexp_line := (Str.regexp_case_fold xs)::!regexp_line; *)
        regexp_line_str := xs::!regexp_line_str;
      end;
    done;
  with _ -> ());
  !line

(* let read_from_debug_file chn : string list = *)
(*  ho_1 "read_from_debug_file" (fun _ -> "?") (pr_list (fun x -> x))read_from_debug_file chn *)

let proc_option str =
  let rec aux str tr_flag lp_flag =
    match str with
      | [] -> (tr_flag,lp_flag)
      | s::str ->
            begin
              if String.compare s "Trace" == 0 then aux str true lp_flag 
              else if String.compare s "Loop" == 0 then aux str tr_flag true 
              else 
                let () = (print_endline ("Warning - wrong debug command :"^s)) 
                in aux str tr_flag lp_flag
            end
  in aux str false false

let rec get_words str =
  let len = String.length str in
  try
    let l = String.index str ',' in
    let m = String.sub str 0 l in
    let rest = String.sub str (l+1) ((len) -l -1) in
    m::(get_words rest)
  with _ -> if len<4 then [] else [str] 

(* let get_words str = *)
(*   let pr_id x = x in *)
(*   ho_1 "get_words" pr_id (pr_list pr_id) get_words str *)

let add_entry_with_options entry_fn xs =
  List.iter (fun x ->
      try
        let l = String.index x ',' in
        let m = String.sub x 0 l in
        let split = String.sub x (l+1) ((String.length x) -l -1) in
        let opts = get_words split in
        (* let (tr_flag,lp_flag) = proc_option opts in *)
        let kind = match proc_option opts with
          | false,false -> DO_Normal
          | false,true -> DO_Loop
          | true,false -> DO_Trace
          | true,true -> DO_Both
        in
        let () = print_endline (m) in
        let () = print_endline (split) in
        (* let kind = if String.compare split "Trace" == 0 then DO_Trace else *)
        (*   if String.compare split "Loop" == 0 then DO_Loop else *)
        (*     DO_Normal *)
        entry_fn m kind
      with _ ->
      entry_fn x DO_Normal
  ) xs

let read_main () =
  let xs = match debug_file() with
    | Some c -> read_from_debug_file c
    | _ -> [] in
  let () = add_entry_with_options (fun x k -> Hashtbl.add debug_map x k) xs in
  let () = add_entry_with_options (fun x k -> 
      let re = Str.regexp_case_fold x 
      in regexp_line := (re,k)::!regexp_line) !regexp_line_str in
  ()
  (* (\* let () = print_endline ((pr_list (fun x -> x)) xs) in *\) *)
  (* List.iter (fun x -> *)
  (*     try *)
  (*       let l = String.index x ',' in *)
  (*       let m = String.sub x 0 l in *)
  (*       let split = String.sub x (l+1) ((String.length x) -l -1) in *)
  (*       let opts = get_words split in *)
  (*       (\* let (tr_flag,lp_flag) = proc_option opts in *\) *)
  (*       let kind = match proc_option opts with *)
  (*         | false,false -> DO_Normal *)
  (*         | false,true -> DO_Loop *)
  (*         | true,false -> DO_Trace *)
  (*         | true,true -> DO_Both *)
  (*       (\* let () = print_endline (m) in *\) *)
  (*       (\* let () = print_endline (split) in *\) *)
  (*       (\* let kind = if String.compare split "Trace" == 0 then DO_Trace else *\) *)
  (*       (\*   if String.compare split "Loop" == 0 then DO_Loop else *\) *)
  (*       (\*     DO_Normal *\) *)
  (*       in *)
  (*       Hashtbl.add debug_map m kind *)
  (*     with _ -> *)
  (*     Hashtbl.add debug_map x DO_Normal *)
  (* ) xs *)

let in_debug x =
  let x = String.trim x in
  let opt_k = 
    try
      Some(List.find (fun (re,k) -> Str.string_match re x 0) !regexp_line)
    with _ -> None in
  match opt_k with
    | Some (_,k) -> k
    | None ->
          begin
            try
              Hashtbl.find debug_map x
            with _ -> DO_None
          end

let go_1 t_flag l_flag s = ho_1_opt_aux t_flag [] l_flag (fun _ -> true) None s
let go_2 t_flag l_flag s = ho_2_opt_aux t_flag [] l_flag (fun _ -> true) None s
let go_3 t_flag l_flag s = ho_3_opt_aux t_flag [] l_flag (fun _ -> true) None s
let go_4 t_flag l_flag s = ho_4_opt_aux t_flag [] l_flag (fun _ -> true) None s
let go_5 t_flag l_flag s = ho_5_opt_aux t_flag [] l_flag (fun _ -> true) None s
let go_6 t_flag l_flag s = ho_6_opt_aux t_flag [] l_flag (fun _ -> true) None s
let go_7 t_flag l_flag s = ho_7_opt_aux t_flag [] l_flag (fun _ -> true) None s

(* let ho_1 s = go_1 false false s *)
(* let ho_2 s = go_2 false false s *)
(* let ho_3 s = go_3 false false s *)
(* let ho_4 s = go_4 false false s *)
(* let ho_5 s = go_5 false false s *)
(* let ho_6 s = go_6 false false s *)
(* let ho_7 s = go_7 false false s *)

(* let to_1 s = go_1 true false s *)
(* let to_2 s = go_2 true false s *)
(* let to_3 s = go_3 true false s *)
(* let to_4 s = go_4 true false s *)
(* let to_5 s = go_5 true false s *)
(* let to_6 s = go_6 true false s *)
(* let to_7 s = go_7 true false s *)

(* let ho_1_loop s = go_1 false true s *)
(* let ho_2_loop s = go_2 false true s *)
(* let ho_3_loop s = go_3 false true s *)
(* let ho_4_loop s = go_4 false true s *)
(* let ho_5_loop s = go_5 false true s *)
(* let ho_6_loop s = go_6 false true s *)
(* let ho_7_loop s = go_7 false true s *)

(* let ho_1 s = ho_1_opt_aux false [] false (fun _ -> true) None s *)
(* let ho_2 s = ho_2_opt_aux false [] false (fun _ -> true) None s *)
(* let ho_3 s = ho_3_opt_aux false [] false (fun _ -> true) None s *)
(* let ho_4 s = ho_4_opt_aux false [] false (fun _ -> true) None s *)
(* let ho_5 s = ho_5_opt_aux false [] false (fun _ -> true) None s *)
(* let ho_6 s = ho_6_opt_aux false [] false (fun _ -> true) None s *)
(* let ho_7 s = ho_7_opt_aux false [] false (fun _ -> true) None s *)

(* let to_1 s = ho_1_opt_aux true [] false (fun _ -> true) None s *)
(* let to_2 s = ho_2_opt_aux true [] false (fun _ -> true) None s *)
(* let to_3 s = ho_3_opt_aux true [] false (fun _ -> true) None s *)
(* let to_4 s = ho_4_opt_aux true [] false (fun _ -> true) None s *)
(* let to_5 s = ho_5_opt_aux true [] false (fun _ -> true) None s *)
(* let to_6 s = ho_6_opt_aux true [] false (fun _ -> true) None s *)
(* let to_7 s = ho_7_opt_aux true [] false (fun _ -> true) None s *)

(* let ho_1_loop s = ho_1_opt_aux false [] true (fun _ -> true) None s *)
(* let ho_2_loop s = ho_2_opt_aux false [] true (fun _ -> true) None s *)
(* let ho_3_loop s = ho_3_opt_aux false [] true (fun _ -> true) None s *)
(* let ho_4_loop s = ho_4_opt_aux false [] true (fun _ -> true) None s *)
(* let ho_5_loop s = ho_5_opt_aux false [] true (fun _ -> true) None s *)
(* let ho_6_loop s = ho_6_opt_aux false [] true (fun _ -> true) None s *)
(* let ho_7_loop s = ho_7_opt_aux false [] true (fun _ -> true) None s *)

let splitter s f_none f_gen f_norm =
  if !z_debug_flag then
    match (in_debug s) with
      | DO_Normal -> f_gen (f_norm false false)
      | DO_Trace -> f_gen (f_norm true false) 
      | DO_Loop -> f_gen (f_norm false true)
      | DO_Both -> f_gen (f_norm true true)
      | DO_None -> f_none
  else f_none

let no_1 s p1 p0 f =
  let code_gen fn = fn s p1 p0 f in
  let code_none = ho_aux_no f in
  splitter s code_none code_gen go_1 

let no_2 s p1 p2 p0 f e1 =
  let code_gen fn = fn s p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen go_2

let no_3 s p1 p2 p3 p0 f e1 e2 =
  let code_gen fn = fn s p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen go_3

let no_4 s p1 p2 p3 p4 p0 f e1 e2 e3 =
  let code_gen fn = fn s p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen go_4

let no_5 s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let code_gen fn = fn s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen go_5

let no_6 s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let code_gen fn = fn s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen go_6

let no_7 s p1 p2 p3 p4 p5 p6 p7 p0 f e1 e2 e3 e4 e5 e6 =
  let code_gen fn = fn s p1 p2 p3 p4 p5 p6 p7 p0 f e1 e2 e3 e4 e5 e6 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5 e6) in
  splitter s code_none code_gen go_7


let ho_1_opt tr_flag lp_flag f = ho_1_opt_aux tr_flag [] lp_flag f None
let ho_2_opt tr_flag lp_flag f = ho_2_opt_aux tr_flag [] lp_flag f None
let ho_3_opt tr_flag lp_flag f = ho_3_opt_aux tr_flag [] lp_flag f None
let ho_4_opt tr_flag lp_flag f = ho_4_opt_aux tr_flag [] lp_flag f None
let ho_5_opt tr_flag lp_flag f = ho_5_opt_aux tr_flag [] lp_flag f None
let ho_6_opt tr_flag lp_flag f = ho_6_opt_aux tr_flag [] lp_flag f None

(* let ho_1_opt f = ho_1_opt_aux false [] false f None *)
(* let ho_2_opt f = ho_2_opt_aux false [] false f None *)
(* let ho_3_opt f = ho_3_opt_aux false [] false f None *)
(* let ho_4_opt f = ho_4_opt_aux false [] false f None *)
(* let ho_5_opt f = ho_5_opt_aux false [] false f None *)
(* let ho_6_opt f = ho_6_opt_aux false [] false f None *)

(* let to_1_opt f = ho_1_opt_aux true [] false f None *)
(* let to_2_opt f = ho_2_opt_aux true [] false f None *)
(* let to_3_opt f = ho_3_opt_aux true [] false f None *)
(* let to_4_opt f = ho_4_opt_aux true [] false f None *)
(* let to_5_opt f = ho_5_opt_aux true [] false f None *)
(* let to_6_opt f = ho_6_opt_aux true [] false f None *)
(* let to_7_opt f = ho_7_opt_aux true [] false f None *)

(* let no_1_opt _ _ _ _ f  *)
(*       = ho_aux_no f *)
(* let no_2_opt _ _ _ _ _ f e1  *)
(*       = ho_aux_no (f e1) *)
(* let no_3_opt _ _ _ _ _ _ f e1 e2  *)
(*       = ho_aux_no (f e1 e2) *)
(* let no_4_opt _ _ _ _ _ _ _ f e1 e2 e3  *)
(*       = ho_aux_no (f e1 e2 e3) *)
(* let no_5_opt _ _ _ _ _ _ _ _ f e1 e2 e3 e4  *)
(*       = ho_aux_no (f e1 e2 e3 e4) *)
(* let no_6_opt _ _ _ _ _ _ _ _ _ f e1 e2 e3 e4 e5  *)
(*       = ho_aux_no (f e1 e2 e3 e4 e5) *)

let no_1_opt op s p1 p0 f =
  let code_gen fn = fn op s p1 p0 f in
  let code_none = ho_aux_no (f) in
  splitter s code_none code_gen ho_1_opt

let no_2_opt op s p1 p2 p0 f e1 =
  let code_gen fn = fn op s p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen ho_2_opt

let no_3_opt op s p1 p2 p3 p0 f e1 e2 =
  let code_gen fn = fn op s p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen ho_3_opt

let no_4_opt op s p1 p2 p3 p4 p0 f e1 e2 e3 =
  let code_gen fn = fn op s p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen ho_4_opt

let no_5_opt op s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let code_gen fn = fn op s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen ho_5_opt

let no_6_opt op s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let code_gen fn = fn op s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen ho_6_opt

let add_num f i s = let str=(s^"#"^(string_of_int i)) in f str

let go_1_num tr_flag lp_flag i =  add_num (go_1 tr_flag lp_flag) i
let go_2_num tr_flag lp_flag i =  add_num (go_2 tr_flag lp_flag) i
let go_3_num tr_flag lp_flag i =  add_num (go_3 tr_flag lp_flag) i
let go_4_num tr_flag lp_flag i =  add_num (go_4 tr_flag lp_flag) i
let go_5_num tr_flag lp_flag i =  add_num (go_5 tr_flag lp_flag) i
let go_6_num tr_flag lp_flag i =  add_num (go_6 tr_flag lp_flag) i

let add_num_opt f i p s = let str=(s^"#"^(string_of_int i)) in f p str

let go_1_num_opt tr_flag lp_flag i =  add_num_opt (ho_1_opt tr_flag lp_flag) i
let go_2_num_opt tr_flag lp_flag i =  add_num_opt (ho_2_opt tr_flag lp_flag) i
let go_3_num_opt tr_flag lp_flag i =  add_num_opt (ho_3_opt tr_flag lp_flag) i
let go_4_num_opt tr_flag lp_flag i =  add_num_opt (ho_4_opt tr_flag lp_flag) i
let go_5_num_opt tr_flag lp_flag i =  add_num_opt (ho_5_opt tr_flag lp_flag) i
let go_6_num_opt tr_flag lp_flag i =  add_num_opt (ho_6_opt tr_flag lp_flag) i

(* let ho_1_num i =  add_num ho_1 i *)
(* let ho_2_num i =  add_num ho_2 i *)
(* let ho_3_num i =  add_num ho_3 i *)
(* let ho_4_num i =  add_num ho_4 i *)
(* let ho_5_num i =  add_num ho_5 i *)
(* let ho_6_num i =  add_num ho_6 i *)

(* let to_1_num i =  add_num to_1 i *)
(* let to_2_num i =  add_num to_2 i *)
(* let to_3_num i =  add_num to_3 i *)
(* let to_4_num i =  add_num to_4 i *)
(* let to_5_num i =  add_num to_5 i *)
(* let to_6_num i =  add_num to_6 i *)

(* let ho_1_loop_num i =  add_num ho_1_loop i *)
(* let ho_2_loop_num i =  add_num ho_2_loop i *)
(* let ho_3_loop_num i =  add_num ho_3_loop i *)
(* let ho_4_loop_num i =  add_num ho_4_loop i *)
(* let ho_5_loop_num i =  add_num ho_5_loop i *)
(* let ho_6_loop_num i =  add_num ho_6_loop i *)

let to_1_loop s = ho_1_opt_aux true [] true (fun _ -> true) None s
let to_2_loop s = ho_2_opt_aux true [] true (fun _ -> true) None s
let to_3_loop s = ho_3_opt_aux true [] true (fun _ -> true) None s
let to_4_loop s = ho_4_opt_aux true [] true (fun _ -> true) None s
let to_5_loop s = ho_5_opt_aux true [] true (fun _ -> true) None s
let to_6_loop s = ho_6_opt_aux true [] true (fun _ -> true) None s

let to_1_loop_num i =  add_num to_1_loop i
let to_2_loop_num i =  add_num to_2_loop i
let to_3_loop_num i =  add_num to_3_loop i
let to_4_loop_num i =  add_num to_4_loop i
let to_5_loop_num i =  add_num to_5_loop i
let to_6_loop_num i =  add_num to_6_loop i

(* let no_1_num (i:int) s _ _ f *)
(*       = ho_aux_no f *)
(* let no_2_num (i:int) s _ _ _ f e1 *)
(*       = ho_aux_no (f e1) *)
(* let no_3_num (i:int) s _ _ _ _ f e1 e2 *)
(*       = ho_aux_no (f e1 e2) *)
(* let no_4_num (i:int) s _ _ _ _ _ f e1 e2 e3 *)
(*       = ho_aux_no (f e1 e2 e3) *)
(* let no_5_num (i:int) s _ _ _ _ _ _ f e1 e2 e3 e4 *)
(*       = ho_aux_no (f e1 e2 e3 e4) *)
(* let no_6_num (i:int) s _ _ _ _ _ _ _ f e1 e2 e3 e4 e5 *)
(*       = ho_aux_no (f e1 e2 e3 e4 e5) *)

let no_1_num_opt (i:int) p s p1 p0 f =
  let code_gen fn = fn i p s p1 p0 f in
  let code_none = ho_aux_no f in
  splitter s code_none code_gen go_1_num_opt 

let no_2_num_opt (i:int) p s p1 p2 p0 f e1 =
  let code_gen fn = fn i p s p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen go_2_num_opt 

let no_3_num_opt (i:int) p s p1 p2 p3 p0 f e1 e2 =
  let code_gen fn = fn i p s p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen go_3_num_opt 

let no_4_num_opt (i:int) p s p1 p2 p3 p4 p0 f e1 e2 e3 =
  let code_gen fn = fn i p s p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen go_4_num_opt 

let no_5_num_opt (i:int) p s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let code_gen fn = fn i p s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen go_5_num_opt 

let no_6_num_opt (i:int) p s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let code_gen fn = fn i p s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen go_6_num_opt 

let no_1_num (i:int) s p1 p0 f =
  let code_gen fn = fn i s p1 p0 f in
  let code_none = ho_aux_no f in
  splitter s code_none code_gen go_1_num 

let no_2_num (i:int) s p1 p2 p0 f e1 =
  let code_gen fn = fn i s p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen go_2_num 

let no_3_num (i:int) s p1 p2 p3 p0 f e1 e2 =
  let code_gen fn = fn i s p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen go_3_num 

let no_4_num (i:int) s p1 p2 p3 p4 p0 f e1 e2 e3 =
  let code_gen fn = fn i s p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen go_4_num 

let no_5_num (i:int) s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let code_gen fn = fn i s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen go_5_num 

let no_6_num (i:int) s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let code_gen fn = fn i s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen go_6_num 

let ho_1_cmp tr_flag lp_flag g = ho_1_opt_aux tr_flag [] lp_flag (fun _ -> true) (Some g) 
let ho_2_cmp tr_flag lp_flag g = ho_2_opt_aux tr_flag [] lp_flag (fun _ -> true) (Some g) 
let ho_3_cmp tr_flag lp_flag g = ho_3_opt_aux tr_flag [] lp_flag (fun _ -> true) (Some g) 
let ho_4_cmp tr_flag lp_flag g = ho_4_opt_aux tr_flag [] lp_flag (fun _ -> true) (Some g) 
let ho_5_cmp tr_flag lp_flag g = ho_5_opt_aux tr_flag [] lp_flag (fun _ -> true) (Some g) 
let ho_6_cmp tr_flag lp_flag g = ho_6_opt_aux tr_flag [] lp_flag (fun _ -> true) (Some g) 

(* let ho_1_cmp g = ho_1_opt_aux false [] false (fun _ -> true) (Some g)  *)
(* let ho_2_cmp g = ho_2_opt_aux false [] false (fun _ -> true) (Some g)  *)
(* let ho_3_cmp g = ho_3_opt_aux false [] false (fun _ -> true) (Some g)  *)
(* let ho_4_cmp g = ho_4_opt_aux false [] false (fun _ -> true) (Some g)  *)
(* let ho_5_cmp g = ho_5_opt_aux false [] false (fun _ -> true) (Some g)  *)
(* let ho_6_cmp g = ho_6_opt_aux false [] false (fun _ -> true) (Some g)  *)

(* let to_1_cmp g = ho_1_opt_aux true [] false (fun _ -> true) (Some g)  *)
(* let to_2_cmp g = ho_2_opt_aux true [] false (fun _ -> true) (Some g)  *)
(* let to_3_cmp g = ho_3_opt_aux true [] false (fun _ -> true) (Some g)  *)
(* let to_4_cmp g = ho_4_opt_aux true [] false (fun _ -> true) (Some g)  *)
(* let to_5_cmp g = ho_5_opt_aux true [] false (fun _ -> true) (Some g)  *)
(* let to_6_cmp g = ho_6_opt_aux true [] false (fun _ -> true) (Some g)  *)

(* let ho_1_cmp_loop g = ho_1_opt_aux false [] true (fun _ -> true) (Some g)  *)
(* let ho_2_cmp_loop g = ho_2_opt_aux false [] true (fun _ -> true) (Some g)  *)
(* let ho_3_cmp_loop g = ho_3_opt_aux false [] true (fun _ -> true) (Some g)  *)
(* let ho_4_cmp_loop g = ho_4_opt_aux false [] true (fun _ -> true) (Some g)  *)
(* let ho_5_cmp_loop g = ho_5_opt_aux false [] true (fun _ -> true) (Some g)  *)
(* let ho_6_cmp_loop g = ho_6_opt_aux false [] true (fun _ -> true) (Some g)  *)

let no_1_cmp g s p1 p0 f =
  let code_gen fn = fn g s p1 p0 f in
  let code_none = ho_aux_no f in
  splitter s code_none code_gen ho_1_cmp 

let no_2_cmp g s p1 p2 p0 f e1 =
  let code_gen fn = fn g s p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen ho_2_cmp 

let no_3_cmp g s p1 p2 p3 p0 f e1 e2 =
  let code_gen fn = fn g s p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen ho_3_cmp 

let no_4_cmp g s p1 p2 p3 p4 p0 f e1 e2 e3 =
  let code_gen fn = fn g s p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen ho_4_cmp 

let no_5_cmp g s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let code_gen fn = fn g s p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen ho_5_cmp 

let no_6_cmp g s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let code_gen fn = fn g s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen ho_6_cmp 

(* let no_6_cmp g s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 = *)
(*   let code_gen fn = fn g s p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in *)
(*   let code_none = ho_aux_no (f e1 e2 e3 e4 p5) in *)
(*   splitter s code_none code_gen ho_6_cmp to_6_cmp ho_6_cmp_loop *)

(* let no_1_cmp _ _ _ _ f  *)
(*       = ho_aux_no f *)
(* let no_2_cmp _ _ _ _ _ f e1  *)
(*       = ho_aux_no (f e1) *)
(* let no_3_cmp _ _ _ _ _ _ f e1 e2  *)
(*       = ho_aux_no (f e1 e2) *)
(* let no_4_cmp _ _ _ _ _ _ _ f e1 e2 e3  *)
(*       = ho_aux_no (f e1 e2 e3) *)
(* let no_5_cmp _ _ _ _ _ _ _ _ f e1 e2 e3 e4  *)
(*       = ho_aux_no (f e1 e2 e3 e4) *)
(* let no_6_cmp _ _ _ _ _ _ _ _ _ f e1 e2 e3 e4 e5  *)
(*       = ho_aux_no (f e1 e2 e3 e4 e5) *)

let ho_eff_1 tr_flag lp_flag s l = ho_1_opt_aux tr_flag l lp_flag (fun _ -> true) None s
let ho_eff_2 tr_flag lp_flag s l = ho_2_opt_aux tr_flag l lp_flag (fun _ -> true) None s
let ho_eff_3 tr_flag lp_flag s l = ho_3_opt_aux tr_flag l lp_flag (fun _ -> true) None s
let ho_eff_4 tr_flag lp_flag s l = ho_4_opt_aux tr_flag l lp_flag (fun _ -> true) None s
let ho_eff_5 tr_flag lp_flag s l = ho_5_opt_aux tr_flag l lp_flag (fun _ -> true) None s
let ho_eff_6 tr_flag lp_flag s l = ho_6_opt_aux tr_flag l lp_flag (fun _ -> true) None s

(* let ho_eff_1 s l = ho_1_opt_aux false l false (fun _ -> true) None s *)
(* let ho_eff_2 s l = ho_2_opt_aux false l false (fun _ -> true) None s *)
(* let ho_eff_3 s l = ho_3_opt_aux false l false (fun _ -> true) None s *)
(* let ho_eff_4 s l = ho_4_opt_aux false l false (fun _ -> true) None s *)
(* let ho_eff_5 s l = ho_5_opt_aux false l false (fun _ -> true) None s *)
(* let ho_eff_6 s l = ho_6_opt_aux false l false (fun _ -> true) None s *)

(* let ho_eff_1_loop s l = ho_1_opt_aux false l true (fun _ -> true) None s *)
(* let ho_eff_2_loop s l = ho_2_opt_aux false l true (fun _ -> true) None s *)
(* let ho_eff_3_loop s l = ho_3_opt_aux false l true (fun _ -> true) None s *)
(* let ho_eff_4_loop s l = ho_4_opt_aux false l true (fun _ -> true) None s *)
(* let ho_eff_5_loop s l = ho_5_opt_aux false l true (fun _ -> true) None s *)
(* let ho_eff_6_loop s l = ho_6_opt_aux false l true (fun _ -> true) None s *)

(* let to_eff_1 s l = ho_1_opt_aux true l false (fun _ -> true) None s *)
(* let to_eff_2 s l = ho_2_opt_aux true l false (fun _ -> true) None s *)
(* let to_eff_3 s l = ho_3_opt_aux true l false (fun _ -> true) None s *)
(* let to_eff_4 s l = ho_4_opt_aux true l false (fun _ -> true) None s *)
(* let to_eff_5 s l = ho_5_opt_aux true l false (fun _ -> true) None s *)
(* let to_eff_6 s l = ho_6_opt_aux true l false (fun _ -> true) None s *)

(* let no_eff_1 _ _ _ _ f  *)
(*       = ho_aux_no f *)

let no_eff_1 s l p1 p0 f =
  let code_gen fn = fn s l p1 p0 f in
  let code_none = ho_aux_no f in
  splitter s code_none code_gen ho_eff_1 

let no_eff_2 s l p1 p2 p0 f e1 =
  let code_gen fn = fn s l p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen ho_eff_2 

let no_eff_3 s l p1 p2 p3 p0 f e1 e2 =
  let code_gen fn = fn s l p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen ho_eff_3 

let no_eff_4 s l p1 p2 p3 p4 p0 f e1 e2 e3 =
  let code_gen fn = fn s l p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen ho_eff_4 

let no_eff_5 s l p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let code_gen fn = fn s l p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen ho_eff_5 

let no_eff_6 s l p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let code_gen fn = fn s l p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen ho_eff_6 

(* let no_eff_2 _ _ _ _ _ f e1  *)
(*       = ho_aux_no (f e1) *)
(* let no_eff_3 _ _ _ _ _ _ f e1 e2  *)
(*       = ho_aux_no (f e1 e2) *)
(* let no_eff_4 _ _ _ _ _ _ _ f e1 e2 e3  *)
(*       = ho_aux_no (f e1 e2 e3) *)
(* let no_eff_5 _ _ _ _ _ _ _ _ f e1 e2 e3 e4  *)
(*       = ho_aux_no (f e1 e2 e3 e4) *)
(* let no_eff_6 _ _ _ _ _ _ _ _ _ f e1 e2 e3 e4 e5  *)
(*       = ho_aux_no (f e1 e2 e3 e4 e5) *)

let ho_eff_1_num tr_flag lp_flag i =  add_num (ho_eff_1 tr_flag lp_flag) i
let ho_eff_2_num tr_flag lp_flag i =  add_num (ho_eff_2 tr_flag lp_flag) i
let ho_eff_3_num tr_flag lp_flag i =  add_num (ho_eff_3 tr_flag lp_flag) i
let ho_eff_4_num tr_flag lp_flag i =  add_num (ho_eff_4 tr_flag lp_flag) i
let ho_eff_5_num tr_flag lp_flag i =  add_num (ho_eff_5 tr_flag lp_flag) i
let ho_eff_6_num tr_flag lp_flag i =  add_num (ho_eff_6 tr_flag lp_flag) i

(* let ho_eff_1_num_loop i =  add_num ho_eff_1_loop i *)
(* let ho_eff_2_num_loop i =  add_num ho_eff_2_loop i *)
(* let ho_eff_3_num_loop i =  add_num ho_eff_3_loop i *)
(* let ho_eff_4_num_loop i =  add_num ho_eff_4_loop i *)
(* let ho_eff_5_num_loop i =  add_num ho_eff_5_loop i *)
(* let ho_eff_6_num_loop i =  add_num ho_eff_6_loop i *)

(* let ho_eff_1_num i =  add_num ho_eff_1 i *)
(* let ho_eff_2_num i =  add_num ho_eff_2 i *)
(* let ho_eff_3_num i =  add_num ho_eff_3 i *)
(* let ho_eff_4_num i =  add_num ho_eff_4 i *)
(* let ho_eff_5_num i =  add_num ho_eff_5 i *)
(* let ho_eff_6_num i =  add_num ho_eff_6 i *)

(* let to_eff_1_num i =  add_num to_eff_1 i *)
(* let to_eff_2_num i =  add_num to_eff_2 i *)
(* let to_eff_3_num i =  add_num to_eff_3 i *)
(* let to_eff_4_num i =  add_num to_eff_4 i *)
(* let to_eff_5_num i =  add_num to_eff_5 i *)
(* let to_eff_6_num i =  add_num to_eff_6 i *)

let no_eff_1_num i s l p1 p0 f =
  let code_gen fn = fn i s l p1 p0 f in
  let code_none = ho_aux_no f in
  splitter s code_none code_gen ho_eff_1_num 

let no_eff_2_num i s l p1 p2 p0 f e1 =
  let code_gen fn = fn i s l p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen ho_eff_2_num 

let no_eff_3_num i s l p1 p2 p3 p0 f e1 e2 =
  let code_gen fn = fn i s l p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen ho_eff_3_num 

let no_eff_4_num i s l p1 p2 p3 p4 p0 f e1 e2 e3 =
  let code_gen fn = fn i s l p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen ho_eff_4_num 

let no_eff_5_num i s l p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let code_gen fn = fn i s l p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen ho_eff_5_num 

let no_eff_6_num i s l p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let code_gen fn = fn i s l p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen ho_eff_6_num 

let ho_1_all tr_flag lp_flag s pf gf l = ho_1_opt_aux tr_flag l lp_flag pf gf s
let ho_2_all tr_flag lp_flag s pf gf l = ho_2_opt_aux tr_flag l lp_flag pf gf s
let ho_3_all tr_flag lp_flag s pf gf l = ho_3_opt_aux tr_flag l lp_flag pf gf s
let ho_4_all tr_flag lp_flag s pf gf l = ho_4_opt_aux tr_flag l lp_flag pf gf s
let ho_5_all tr_flag lp_flag s pf gf l = ho_5_opt_aux tr_flag l lp_flag pf gf s
let ho_6_all tr_flag lp_flag s pf gf l = ho_6_opt_aux tr_flag l lp_flag pf gf s

let ho_1_all_num tr_flag lp_flag i =  add_num (ho_1_all tr_flag lp_flag) i
let ho_2_all_num tr_flag lp_flag i =  add_num (ho_2_all tr_flag lp_flag) i
let ho_3_all_num tr_flag lp_flag i =  add_num (ho_3_all tr_flag lp_flag) i
let ho_4_all_num tr_flag lp_flag i =  add_num (ho_4_all tr_flag lp_flag) i
let ho_5_all_num tr_flag lp_flag i =  add_num (ho_5_all tr_flag lp_flag) i
let ho_6_all_num tr_flag lp_flag i =  add_num (ho_6_all tr_flag lp_flag) i

let no_1_all i s pf gf l p1 p0 f =
  let pf = match pf with 
      Some p -> p 
    | _ -> fun _ -> true in
  let code_gen fn = fn i s pf gf l p1 p0 f in
  let code_none = ho_aux_no (f) in
  splitter s code_none code_gen ho_1_all_num 

let no_2_all i s pf gf l p1 p2 p0 f e1 =
  let pf = match pf with 
      Some p -> p 
    | _ -> fun _ -> true in
  let code_gen fn = fn i s pf gf l p1 p2 p0 f e1 in
  let code_none = ho_aux_no (f e1) in
  splitter s code_none code_gen ho_2_all_num 

let no_3_all i s pf gf l p1 p2 p3 p0 f e1 e2 =
  let pf = match pf with 
      Some p -> p 
    | _ -> fun _ -> true in
  let code_gen fn = fn i s pf gf l p1 p2 p3 p0 f e1 e2 in
  let code_none = ho_aux_no (f e1 e2) in
  splitter s code_none code_gen ho_3_all_num 

let no_4_all i s pf gf l p1 p2 p3 p4 p0 f e1 e2 e3 =
  let pf = match pf with 
      Some p -> p 
    | _ -> fun _ -> true in
  let code_gen fn = fn i s pf gf l p1 p2 p3 p4 p0 f e1 e2 e3 in
  let code_none = ho_aux_no (f e1 e2 e3) in
  splitter s code_none code_gen ho_4_all_num 

let no_5_all i s pf gf l p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 =
  let pf = match pf with 
      Some p -> p 
    | _ -> fun _ -> true in
  let code_gen fn = fn i s pf gf l p1 p2 p3 p4 p5 p0 f e1 e2 e3 e4 in
  let code_none = ho_aux_no (f e1 e2 e3 e4) in
  splitter s code_none code_gen ho_5_all_num 

let no_6_all i s pf gf l p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 =
  let pf = match pf with 
      Some p -> p 
    | _ -> fun _ -> true in
  let code_gen fn = fn i s pf gf l p1 p2 p3 p4 p5 p6 p0 f e1 e2 e3 e4 e5 in
  let code_none = ho_aux_no (f e1 e2 e3 e4 e5) in
  splitter s code_none code_gen ho_6_all_num 

(* let no_eff_1_num _ _ _ _ _ f  *)
(*       =  ho_aux_no (f) *)
(* let no_eff_2_num _ _ _ _ _ _ f e1  *)
(*       =  ho_aux_no (f e1) *)
(* let no_eff_3_num _ _ _ _ _ _ _ f e1 e2  *)
(*       =  ho_aux_no (f e1 e2) *)
(* let no_eff_4_num _ _ _ _ _ _ _ _ f e1 e2 e3  *)
(*       =  ho_aux_no (f e1 e2 e3) *)
(* let no_eff_5_num _ _ _ _ _ _ _ _ _ f e1 e2 e3 e4  *)
(*       =  ho_aux_no (f e1 e2 e3 e4) *)
(* let no_eff_6_num _ _ _ _ _ _ _ _ _ _ f e1 e2 e3 e4 e5  *)
(*       =  ho_aux_no (f e1 e2 e3 e4 e5) *)

(* let no_1_loop _ _ _ f  *)
(*       = ho_aux_no f *)
(* let no_2_loop _ _ _ _ f e1  *)
(*       = ho_aux_no (f e1) *)
(* let no_3_loop _ _ _ _ _ f e1 e2 *)
(*       = ho_aux_no (f e1 e2) *)
(* let no_4_loop _ _ _ _ _ _ f e1 e2 e3 *)
(*       = ho_aux_no (f e1 e2 e3) *)
(* let no_5_loop _ _ _ _ _ _ _ f e1 e2 e3 e4 *)
(*       = ho_aux_no (f e1 e2 e3 e4) *)
(* let no_6_loop _ _ _ _ _ _ _ _ f e1 e2 e3 e4 e5 *)
(*       = ho_aux_no (f e1 e2 e3 e4 e5) *)


(* let no_1_loop_num _ _ _ _ f  *)
(*       = ho_aux_no f *)
(* let no_2_loop_num _ _ _ _ _ f e1  *)
(*       = ho_aux_no (f e1) *)
(* let no_3_loop_num _ _ _ _ _ _ f e1 e2 *)
(*       = ho_aux_no (f e1 e2) *)
(* let no_4_loop_num _ _ _ _ _ _ _ f e1 e2 e3 *)
(*       = ho_aux_no (f e1 e2 e3) *)
(* let no_5_loop_num _ _ _ _ _ _ _ _ f e1 e2 e3 e4 *)
(*       = ho_aux_no (f e1 e2 e3 e4) *)
(* let no_6_loop_num _ _ _ _ _ _ _ _ _ f e1 e2 e3 e4 e5 *)
(*       = ho_aux_no (f e1 e2 e3 e4 e5) *)

  (* let no_eff_1_opt  _ _ _ _ _ f = f *)
  (* let no_eff_2_opt  _ _ _ _ _ _ f = f *)
  (* let no_eff_3_opt  _ _ _ _ _ _ _ f = f *)
  (* let no_eff_4_opt  _ _ _ _ _ _ _ _ f = f *)
  (* let no_eff_5_opt  _ _ _ _ _ _ _ _ _ f = f *)
  (* let no_eff_6_opt  _ _ _ _ _ _ _ _ _ _ f = f *)

end

module DebugEmpty  =
struct
  let z_debug_file = ref ""
    (* let z_debug_regexp = ref None *)
  let z_debug_flag = ref false

  let read_main() = ()
  let no_1 s p1 p0 f = f
  let no_2 s p1 p2 p0 f = f
  let no_3 s p1 p2 p3 p0 f = f
  let no_4 s p1 p2 p3 p4 p0 f = f
  let no_5 s p1 p2 p3 p4 p5 p0 f = f
  let no_6 s p1 p2 p3 p4 p5 p6 p0 f = f
  let no_7 s p1 p2 p3 p4 p5 p6 p7 p0 f = f

  let no_1_cmp g s p1 p0 f = f
  let no_2_cmp g s p1 p2 p0 f = f
  let no_3_cmp g s p1 p2 p3 p0 f = f
  let no_4_cmp g s p1 p2 p3 p4 p0 f = f
  let no_5_cmp g s p1 p2 p3 p4 p5 p0 f = f
  let no_6_cmp g s p1 p2 p3 p4 p5 p6 p0 f = f

  let no_1_opt op s p1 p0 f = f
  let no_2_opt op s p1 p2 p0 f = f
  let no_3_opt op s p1 p2 p3 p0 f = f
  let no_4_opt op s p1 p2 p3 p4 p0 f = f
  let no_5_opt op s p1 p2 p3 p4 p5 p0 f = f
  let no_6_opt op s p1 p2 p3 p4 p5 p6 p0 f = f

  let no_eff_1 s l p1 p0 f = f
  let no_eff_2 s l p1 p2 p0 f = f
  let no_eff_3 s l p1 p2 p3 p0 f = f
  let no_eff_4 s l p1 p2 p3 p4 p0 f = f
  let no_eff_5 s l p1 p2 p3 p4 p5 p0 f = f
  let no_eff_6 s l p1 p2 p3 p4 p5 p6 p0 f = f

  let no_eff_1_num i s l p1 p0 f = f
  let no_eff_2_num i s l p1 p2 p0 f = f
  let no_eff_3_num i s l p1 p2 p3 p0 f = f
  let no_eff_4_num i s l p1 p2 p3 p4 p0 f = f
  let no_eff_5_num i s l p1 p2 p3 p4 p5 p0 f = f
  let no_eff_6_num i s l p1 p2 p3 p4 p5 p6 p0 f = f

  let no_1_num (i:int) s p1 p0 f  = f
  let no_2_num (i:int) s p1 p2 p0 f  = f
  let no_3_num (i:int) s p1 p2 p3 p0 f  = f
  let no_4_num (i:int) s p1 p2 p3 p4 p0 f  = f
  let no_5_num (i:int) s p1 p2 p3 p4 p5 p0 f  = f
  let no_6_num (i:int) s p1 p2 p3 p4 p5 p6 p0 f  = f 

  let no_1_num_opt (i:int) p s p1 p0 f =  f
  let no_2_num_opt (i:int) p s p1 p2 p0 f  = f
  let no_3_num_opt (i:int) p s p1 p2 p3 p0 f = f
  let no_4_num_opt (i:int) p s p1 p2 p3 p4 p0 f = f
  let no_5_num_opt (i:int) p s p1 p2 p3 p4 p5 p0 f = f
  let no_6_num_opt (i:int) p s p1 p2 p3 p4 p5 p6 p0 f = f

  let no_1_all (i:int) s l p g p1 p0 f =  f
  let no_2_all (i:int) s l p g p1 p2 p0 f =  f
  let no_3_all (i:int) s l p g p1 p2 p3 p0 f =  f
  let no_4_all (i:int) s l p g p1 p2 p3 p4 p0 f =  f
  let no_5_all (i:int) s l p g p1 p2 p3 p4 p5 p0 f =  f
  let no_6_all (i:int) s l p g p1 p2 p3 p4 p5 p6 p0 f =  f

(*
type: int ->
  string ->
  ('w23 -> bool) option ->
  ('x23 -> 'y23 -> 'z23 -> 'a24 -> 'b24 -> 'w23) option ->
  bool list ->
  ('x23 -> string) ->
  ('y23 -> string) ->
  ('z23 -> string) ->
  ('a24 -> string) ->
  ('b24 -> string) ->
  ('w23 -> string) ->
  ('x23 -> 'y23 -> 'z23 -> 'a24 -> 'b24 -> 'w23) ->
  'x23 -> 'y23 -> 'z23 -> 'a24 -> 'b24 -> 'w23
*)


end

(* include DebugEmpty *)
include DebugCore

