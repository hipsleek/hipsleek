type printing_order =
  | PrintPair
  | PrintChrono

type 'a user_action =
  | UacQuit
  | UacRunAll of ('a list)             (* all actions *)
  | UacRunStep of ('a * 'a list)       (* selected action and the remaining *)

let show_trace_message = ref false

(* debug flag *)
let debug_normal_mode = ref false
let debug_deep_mode = ref false
let debug_silence = ref false

let trace_function_mode = ref false
let trace_debug = ref false
let trace_function_regex =  ref ""
let trace_function_printing_order = ref PrintPair

let proc_call_id = ref 0
let proc_call_stack = Stack.create ()

(* let get_time () = Sys.time () *)

let get_time () = Unix.gettimeofday ()

let has_newline str =
  try
    let _ = Str.search_forward (Str.regexp "\n") str 0 in
    true
  with Not_found -> false

let format_msg msg info =
  let msg = msg in
  if has_newline info then msg ^ "\n" ^ info
  else msg ^ info

let print msg =
  if !debug_silence then ()
  else print_string msg

let println msg =
  if !debug_silence then ()
  else print_endline msg

let new_proc_call_id () =
  let _  = proc_call_id := !proc_call_id + 1 in
  !proc_call_id

let pr_call_stack () =
  let call_stack = ref "" in
  let _ = Stack.iter (fun x ->
    call_stack := "@" ^ (string_of_int x) ^ !call_stack) proc_call_stack in
  !call_stack

let eprint s = println s   (* use println to flush output *)

let record_time f logtimes =
  let time_begin = get_time () in
  let output = f () in
  let time_end = get_time () in
  let time = time_end -. time_begin in
  let _ = logtimes |> List.iter (fun x -> x := !x +. time) in
  (output, time)

(* debug and check invariant *)
let trace_core ?(logtime: (float ref) list = []) ?(showtime=false)
      ?(trace : (string * 'a * ('a -> string) * ('b -> string)) option = None)
      (proc: unit -> 'b) : 'b =
  let run_proc_record_time () =
    if (logtime = []) then (proc (), 0.)
    else if (!trace_function_printing_order = PrintPair) then
      let res, time = record_time proc logtime in
      (res, time)
    else record_time proc logtime in
  let res = match trace with
    | None -> fst (run_proc_record_time ())
    | Some (proc_name, input, pr_in, pr_out) ->
      let regex = Str.regexp !trace_function_regex in
      let old_printing_status = !show_trace_message in
      let new_printing_status =
        if (String.compare !trace_function_regex "" = 0) then false
        else if (Str.string_match regex proc_name 0) then true
        else false in
      let proc_name =
        if new_printing_status then
          let call_id = new_proc_call_id () in
          let _ = Stack.push call_id proc_call_stack in
          proc_name ^ "#" ^ (string_of_int call_id)
          ^ " : " ^ (pr_call_stack ())
        else proc_name in
      if new_printing_status then
        let _ = eprint "\n\n" in
        let _ = eprint "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" in
        let _ = show_trace_message := new_printing_status in
        let tmp =
          let _ = if !show_trace_message then
              eprint (">>> " ^ proc_name ^ "\n" ^ (pr_in input)) in
          let output, time = run_proc_record_time () in
          let _ = if !show_trace_message then (
            eprint ">>>>>>>>>>>>>>>>>>";
            eprint (">>> " ^ proc_name);
            eprint ("### Result: " ^ (pr_out output));
            if (showtime) then
              eprint ("### Time spent: " ^ (Printf.sprintf "%.3f" time) ^ " (s)")) in
          output in
        let _ = show_trace_message := old_printing_status in
        let _ = Stack.pop proc_call_stack in
        tmp
      else fst (run_proc_record_time ()) in
  res


let trace_1 ?(logtime: (float ref) list = []) ?(showtime=false)
    proc_name
    (pr_inout: ('a -> string) * ('b -> string))
    (input: 'a) (proc: unit -> 'b) : 'z =
  if not !trace_debug then proc ()
  else if !trace_function_mode then
    let pr_in, pr_out = pr_inout in
    let pr_in x = "=== Input: " ^ (pr_in x) in
    trace_core ~logtime:logtime ~showtime:showtime
      ~trace:(Some (proc_name, input, pr_in, pr_out)) proc
  else trace_core ~logtime:logtime ~showtime:showtime proc


let trace_2 ?(logtime: (float ref) list = []) ?(showtime=false)
    proc_name
    (pr_inout: ('a1 -> string) * ('a2 -> string) * ('b -> string))
    (input1: 'a1) (input2: 'a2) (proc: unit -> 'b) : 'b =
  if not !trace_debug then proc ()
  else if !trace_function_mode then
    let pr_in1, pr_in2, pr_out = pr_inout in
    let pr_in (x1, x2) =
      "=== Input 1: " ^ (pr_in1 x1) ^ "\n"
      ^ "=== Input 2: " ^ (pr_in2 x2) in
    let input = (input1, input2) in
    trace_core ~logtime:logtime ~showtime:showtime
      ~trace:(Some (proc_name, input, pr_in, pr_out)) proc
  else trace_core ~logtime:logtime ~showtime:showtime proc

let trace_3 ?(logtime: (float ref) list = []) ?(showtime=false)
    proc_name
    (pr_inout: ('a1 -> string) * ('a2 -> string) * ('a3 -> string) *
         ('b -> string))
    (input1: 'a1) (input2: 'a2) (input3: 'a3) (proc: unit -> 'b) : 'b =
  if not !trace_debug then proc ()
  else if !trace_function_mode then
    let pr_in1, pr_in2, pr_in3, pr_out = pr_inout in
    let pr_in (x1, x2, x3) =
      "=== Input 1: " ^ (pr_in1 x1) ^ "\n"
      ^ "=== Input 2: " ^ (pr_in2 x2) ^ "\n"
      ^ "=== Input 3: " ^ (pr_in3 x3) in
    let input = (input1, input2, input3) in
    trace_core ~logtime:logtime ~showtime:showtime
      ~trace:(Some (proc_name, input, pr_in, pr_out)) proc
  else trace_core ~logtime:logtime ~showtime:showtime proc

let trace_4 ?(logtime: (float ref) list = []) ?(showtime=false)
    proc_name
    (pr_inout: ('a1 -> string) * ('a2 -> string) *
         ('a3 -> string) * ('a4 -> string) *
         ('b -> string))
    (input1: 'a1) (input2: 'a2) (input3: 'a3) (input4: 'a4)
    (proc: unit -> 'b) : 'b =
  if not !trace_debug then proc ()
  else if !trace_function_mode then
    let pr_in1, pr_in2, pr_in3, pr_in4, pr_out = pr_inout in
    let pr_in (x1, x2, x3, x4) =
      "=== Input 1: " ^ (pr_in1 x1) ^ "\n"
      ^ "=== Input 2: " ^ (pr_in2 x2) ^ "\n"
      ^ "=== Input 3: " ^ (pr_in3 x3) ^ "\n"
      ^ "=== Input 4: " ^ (pr_in4 x4) in
    let input = (input1, input2, input3, input4) in
    trace_core ~logtime:logtime ~showtime:showtime
      ~trace:(Some (proc_name, input, pr_in, pr_out)) proc
  else trace_core ~logtime:logtime ~showtime:showtime proc

let trace_5 ?(logtime: (float ref) list = []) ?(showtime=false)
    proc_name
    (pr_inout: ('a1 -> string) * ('a2 -> string) *
         ('a3 -> string) * ('a4 -> string) * ('a5 -> string) *
         ('b -> string))
    (input1: 'a1) (input2: 'a2) (input3: 'a3) (input4: 'a4) (input5: 'a5)
    (proc: unit -> 'b) : 'b =
  if not !trace_debug then proc ()
  else if !trace_function_mode then
    let pr_in1, pr_in2, pr_in3, pr_in4, pr_in5, pr_out = pr_inout in
    let pr_in (x1, x2, x3, x4, x5) =
      "=== Input 1: " ^ (pr_in1 x1) ^ "\n"
      ^ "=== Input 2: " ^ (pr_in2 x2) ^ "\n"
      ^ "=== Input 3: " ^ (pr_in3 x3) ^ "\n"
      ^ "=== Input 4: " ^ (pr_in4 x4) ^ "\n"
      ^ "=== Input 5: " ^ (pr_in5 x5) in
    let input = (input1, input2, input3, input4, input5) in
    trace_core ~logtime:logtime ~showtime:showtime
      ~trace:(Some (proc_name, input, pr_in, pr_out)) proc
  else trace_core ~logtime:logtime ~showtime:showtime proc

let trace_6 ?(logtime: (float ref) list = []) ?(showtime=false)
    proc_name
    (pr_inout: ('a1 -> string) * ('a2 -> string) * ('a3 -> string) *
         ('a4 -> string) * ('a5 -> string) * ('a6 -> string) *
         ('b -> string))
    (input1: 'a1) (input2: 'a2) (input3: 'a3)
    (input4: 'a4) (input5: 'a5) (input6: 'a6)
    (proc: unit -> 'b) : 'b =
  if not !trace_debug then proc ()
  else if !trace_function_mode then
    let pr_in1, pr_in2, pr_in3, pr_in4, pr_in5, pr_in6, pr_out = pr_inout in
    let pr_in (x1, x2, x3, x4, x5, x6) =
      "=== Input 1: " ^ (pr_in1 x1) ^ "\n"
      ^ "=== Input 2: " ^ (pr_in2 x2) ^ "\n"
      ^ "=== Input 3: " ^ (pr_in3 x3) ^ "\n"
      ^ "=== Input 4: " ^ (pr_in4 x4) ^ "\n"
      ^ "=== Input 5: " ^ (pr_in5 x5) ^ "\n"
      ^ "=== Input 6: " ^ (pr_in6 x6) in
    let input = (input1, input2, input3, input4, input5, input6) in
    trace_core ~logtime:logtime ~showtime:showtime
      ~trace:(Some (proc_name, input, pr_in, pr_out)) proc
  else trace_core ~logtime:logtime ~showtime:showtime proc

(***********************************************)
(*********       generic printing      *********)

let hprint (msg: string) (f: 'a -> string) (x: 'a) : unit =
  let msg = format_msg ("\n!!! " ^ msg) (f x) in
  println msg

let hprintln = hprint

let dhprint (msg: string) (f: 'a -> string) (x: 'a) : unit =
  let msg = format_msg ("\n!!! " ^ msg) (f x) in
  if (!debug_normal_mode || !debug_deep_mode) then
    println msg
  else ()

let ddhprint (msg: string) (f: 'a -> string) (x: 'a) : unit =
  let msg = format_msg ("\n!!! " ^ msg) (f x) in
  if (!debug_deep_mode) then
    println msg
  else ()

let nhprint msg f x = ()

let pprint (msg: string) : unit =
  let nmsg = "\n!!! " ^ msg in
  println nmsg

let dprint (msg: string) : unit =
  let nmsg = "\n!!! " ^ msg in
  if (!debug_normal_mode || !debug_deep_mode) then println nmsg
  else ()

let ddprint (msg: string) : unit =
  let nmsg = "\n!!! " ^ msg in
  if (!debug_deep_mode) then println nmsg
  else ()

let sprint (msgs: string list) : unit =
  let msg = String.concat "" msgs in
  if (!debug_normal_mode || !debug_deep_mode) then print_endline ("\n" ^ msg)
  else ()

let ndprint msg = ()

let npprint msg = ()

let sprint (msgs: string list) : unit =
  let msg = "\n!!! " ^ (String.concat "" msgs) in
  println msg

let dsprint (msgs: string list) : unit =
  let msg = "\n!!! " ^ (String.concat "" msgs) in
  if (!debug_deep_mode) then println msg
  else ()

let nsprint msg = ()

let rpprint (msg: string) : unit = print_endline ("\n" ^ msg)

let rsprint (msgs: string list) : unit =
  let msg = String.concat "" msgs in
  print_endline ("\n" ^ msg)

let rhprint (msg: string) (f: 'a -> string) (x: 'a) : unit =
  let msg = format_msg msg (f x) in
  print_endline ("\n" ^ msg)

(*************************************************)
(*********       printing with flag      *********)

let fprint (flag: bool) (msg: string) =
  if flag then
    let msg = "\n$$$ >> " ^ msg in
    print msg
  else ()

let fhprint (flag: bool) (msg: string) (f: 'a -> string) (x: 'a) : unit =
  let msg = format_msg msg (f x) in
  fprint flag msg

let fprintln (flag: bool) (msg: string) =
  if flag then
    let msg = "\n$$$ >> " ^ msg in
    println msg
  else ()

let fhprintln (flag: bool) (msg: string) (f: 'a -> string) (x: 'a) : unit =
  let msg = format_msg msg (f x) in
  fprintln flag msg

(*************************************************)
(*********          interactive          *********)


let rec ask_decision question (possible_answers: string list) : string =
  let answer = "[" ^ (String.concat "/" possible_answers) ^ "]" in
  let msg = question ^ " " ^ answer ^ ": " in
  let _ = print_string ("\n$$$>>> " ^ msg) in
  let answer = String.trim (read_line ()) in
  if (List.exists (String.equal answer) possible_answers) then answer
  else
    let _ = print_endline "\n>>> Choose again!" in
    ask_decision question possible_answers
