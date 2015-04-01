#include "xdebug.cppo"
open Gen
open Globals
open VarGen

let trace_timer = false

class timelog =
object (self)
  val time_stk = new Gen.stack_noexc ("dummy",0.) (pr_pair pr_id string_of_float) (==)
  val hist_big = new Gen.stack_pr (pr_pair pr_id string_of_float) (==) 
  val hist_stk = new Gen.stack_pr (pr_pair pr_id string_of_float) (==) 
    (* (fun (s,x) ->  s="kill" || x>=0.5 ) *)
  val stk_t = new Gen.stack_noexc 0. string_of_float (==)
  val mutable last_time = 0. 
  val mutable last_timeout_flag = false
  val mutable timer_val = None
  val mutable timer_timeout_flag = false 
  val mutable last_big = None
  (* method print_timer = "unsure" *)
    (* add_str "timer status" (pr_pair string_of_float (pr_option string_of_int)) (timer,timer_exc) *)
  method timer_start pno s =
    begin
      if trace_timer then print_endline_quiet ("inside timer_start "^pno);
      timer_timeout_flag <- false;
      stk_t # push s
    end
  method timer_stop pno s =
    begin
      (* timer_timeout <- false; *)
      if trace_timer then print_endline_quiet ("inside timer_stop "^pno); 
      let r = stk_t # pop_top_no_exc in
      if stk_t # is_empty then 
        (if timer_val==None then timer_val <- Some s)
      else print_endline_quiet "Nested Timer(stop)"
    end
  method timer_timeout pno s =
    begin
      if trace_timer then print_endline_quiet ("inside timer_timeout "^pno);
      timer_timeout_flag <- true;
      let r = stk_t # pop_top_no_exc in
      if stk_t # is_empty then 
        (if timer_val==None then timer_val <- Some s)
      else print_endline_quiet "Nested Timer(timeout)"
    end
  method start_time s = 
    let t = Gen.Profiling.get_main_time() in
    let () = time_stk # push (s,t) in
    ()

  method add_proof_info new_s no =
    if trace_timer then 
      print_endline_quiet ("inside add_proof_info "^new_s^" "^no);
    match last_big with
      | None -> ()
      | Some(s,t,slk_no) -> 
            begin
              if trace_timer then print_endline_quiet "adding last_big";
              let to_flag = timer_timeout_flag in
              (* let slk_no = get_sleek_no ()) in  *)
              last_big<-None;
              let s2 = if to_flag then ":TIMEOUT:" else ":" in
              (* let s2 = if last_timeout_flag then s2^":T2:" else s2 in *)
               hist_big # push((s^":"^no^"<"^slk_no^s2^new_s),t)
            end


  method stop_time = 
    begin
      let (s,tt) = 
        match timer_val with
          | Some t2 ->
                begin
                  (* let t = Gen.Profiling.get_time() in *)
                  let (s,_) = time_stk # pop_top_no_exc in
                  timer_val <- None;
                  (s,t2)
                end
          | None ->
                let t = Gen.Profiling.get_main_time() in
                let (s,st) = time_stk # pop_top_no_exc in
                (s,t -. st)
      in
      if tt>3.0 then
        begin
          let slkno = get_sleek_no () in
          last_big <- Some (s,tt,(string_of_int slkno))
        end
      else hist_stk # push (s,tt);
      last_time <- tt ; 
      last_timeout_flag <- timer_timeout_flag; 
      tt
    end
  method dump = 
    let prL = (pr_list (fun (_,f) -> string_of_float f)) in
    let prL2 = (pr_list (pr_pair pr_id string_of_float)) in
    let prL = prL2 in
    let c = hist_stk # len in
    let ls = List.rev (hist_stk # get_stk) in
    let bigger = List.rev (hist_big # get_stk) in
    let (big,small) = List.partition (fun (_,x) -> x>=0.5) ls in
    (* let (bigger,big) = List.partition (fun (_,x) -> x>=5.0) big in *)
    let s_big = string_of_int (List.length big) in
    let s_bigger = string_of_int (List.length bigger) in
    let b = List.fold_left (fun c (_,x1) -> c +. x1) 0. big in 
    let bb = List.fold_left (fun c (_,x1) -> c +. x1) 0. bigger in 
    let s = List.fold_left (fun c (_,x1) -> c +. x1)  0. small in 
    (* let (small_mona,small_others) = List.partition (fun (e,x) -> x>=0.5) ls in *)
    if (not (!Globals.web_compile_flag || !Globals.print_min)) then Debug.info_hprint (add_str "log(small)" (pr_pair string_of_float string_of_int )) (s,List.length small) no_pos;
    if not(big==[]) then if (not !Globals.web_compile_flag) then Debug.info_hprint (add_str ("log(big)(>0.5s)("^s_big^")") (pr_pair string_of_float prL)) (b,big) no_pos;
    if not(bigger==[]) then if (not !Globals.web_compile_flag) then Debug.info_hprint (add_str ("\n log(bigger)(>4s)("^s_bigger^")") (pr_pair string_of_float prL2)) (bb,bigger) no_pos;
    ()

  (* method dump =  *)
  (*   Debug.no_1 "dump" pr_none pr_none (fun _ -> self # dump) () *)

  method get_last_time =
    last_time

  method get_last_timeout = 
    last_timeout_flag
  method get_timeout () =
    timer_timeout_flag
end;;

let logtime = new timelog

(* let logtime_wrapper s f x = *)
(*     try *)
(*       let () = logtime # start_time s in *)
(*       let res = f x in *)
(*       let () = logtime # stop_time in *)
(*       res *)
(*     with e -> *)
(*         let tt = logtime # stop_time in  *)
(*         let () = Debug.info_hprint (add_str "WARNING logtime exception" string_of_float) tt no_pos in *)
(*         raise e *)

let log_wrapper s logger f x  =
    try
      let () = logtime # start_time s in
      let res = f x in
      let r = logtime # stop_time in
      let to_flag = logtime # get_timeout () in
      let (pr,no) = logger (Some res) r to_flag in
      (* if s="sleek-hec" then print_endline ("log_wrapper (normal):"^no); *)
      logtime # add_proof_info pr no;
      res
    with e ->
        let tt = logtime # stop_time in 
        let to_flag = logtime # get_timeout () in
        let (pr,no) = logger None tt to_flag in
        logtime # add_proof_info (pr^"*EXC*") no;
        (* if s="sleek-hec" then print_endline ("log_wrapper (exc):"^no); *)
        let () = Debug.info_hprint (add_str "WARNING logtime exception" string_of_float) tt no_pos in
        raise e
