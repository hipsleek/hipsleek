open Globals
open Gen.Basic

let string_of_path_trace x = pr_list (pr_pair (fun x -> "c_id") (fun x -> "p_label")) x

class es_trace =
object
  inherit [path_trace] store [] (string_of_path_trace)
     (* method string_of_string : string = match lc with *)
     (*   | None -> "None" *)
     (*   | Some l -> l *)
end;;

let last_trace  = new es_trace

let wrap_trace (tr : path_trace) exec_function args =
  let b = last_trace # is_avail in
  let m = last_trace # get in
  let _ = last_trace # set tr in
  let res = exec_function args in
  let _ = 
    if b then last_trace # set m 
    else last_trace # reset in
  res

let trace_info () = 
  if(last_trace # is_avail) then
        (" trace::"^(last_trace # string_of))
  else "..."
