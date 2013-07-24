open Gen
open Globals

class timelog =
object (self)
  val time_stk = new Gen.stack_noexc ("dummy",0.) (pr_pair pr_id string_of_float) (==)
  val hist_stk = new Gen.stack_pr (pr_pair pr_id string_of_float) (==) 
    (* (fun (s,x) ->  s="kill" || x>=0.5 ) *)
  val stk_t = new Gen.stack_noexc 0. string_of_float (==)
  val mutable last_time = 0. 
  val mutable last_timeout = false
  val mutable timer_val = None
  val mutable timer_timeout = false
  (* method print_timer = "unsure" *)
    (* add_str "timer status" (pr_pair string_of_float (pr_option string_of_int)) (timer,timer_exc) *)
  method timer_start s =
    begin
      stk_t # push s
    end
  method timer_stop s =
    begin
      timer_timeout <- false;
      let r = stk_t # pop_top in
      if stk_t # is_empty then 
        (if timer_val==None then timer_val <- Some s)
      else print_endline "Nested Timer(stop)"
    end
  method timer_timeout s =
    begin
      timer_timeout <- true;
      let r = stk_t # pop_top in
      if stk_t # is_empty then 
        (if timer_val==None then timer_val <- Some s)
      else print_endline "Nested Timer(timeout)"
    end
  method start_time s = 
    timer_timeout <- false;
    let t = Gen.Profiling.get_time() in
    let _ = time_stk # push (s,t) in
    ()

  method stop_time = 
    begin
      let (s,tt) = 
        match timer_val with
          | Some t2 ->
                begin
                  (* let t = Gen.Profiling.get_time() in *)
                  let (s,_) = time_stk # pop_top in
                  timer_val <- None;
                  (s,t2)
                end
          | None ->
                let t = Gen.Profiling.get_time() in
                let (s,st) = time_stk # pop_top in
                (s,t -. st)
      in
      let _ = hist_stk # push (s,tt) in
      last_time <- tt ; 
      last_timeout <- timer_timeout; 
      tt
    end
  method dump = 
    let prL = (pr_list (fun (_,f) -> string_of_float f)) in
    let c = hist_stk # len in
    let ls = List.rev (hist_stk # get_stk) in
    let (big,small) = List.partition (fun (_,x) -> x>=0.5) ls in
    let b = List.fold_left (fun c (_,x1) -> c +. x1) 0. big in 
    let s= List.fold_left (fun c (_,x1) -> c +. x1)  0. small in 
    Debug.info_hprint (add_str "time_log (small)" (pr_pair string_of_float string_of_int )) (s,List.length small) no_pos;
    Debug.info_hprint (add_str "log (>.5s)" (pr_pair string_of_float prL)) (b,big) no_pos
  method get_last_time = last_time
  method get_last_timeout = last_timeout
end;;

let logtime = new timelog

let logtime_wrapper s f x =
    try
      let _ = logtime # start_time s in
      let res = f x in
      let _ = logtime # stop_time in
      res
    with e ->
        let tt = logtime # stop_time in 
        let _ = Debug.info_hprint (add_str "WARNING logtime exception" string_of_float) tt no_pos in
        raise e

let log_wrapper s logger f x  =
    try
      let _ = logtime # start_time s in
      let res = f x in
      let r = logtime # stop_time in
      logger (Some res) r (logtime # get_last_timeout) ;
      res
    with e ->
        let tt = logtime # stop_time in 
        logger None tt (logtime # get_last_timeout);
        let _ = Debug.info_hprint (add_str "WARNING logtime exception" string_of_float) tt no_pos in
        raise e
