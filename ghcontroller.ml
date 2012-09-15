open Globals
open GUtil
(**/**)
module MU = Mainutil
module TC = Typechecker
module CA = Cast
(**/**)

(**
   Helper for interacting with Hip script
   Command calling, process management, parsing of result,...
 *)
module HipHelper = struct

  open SourceUtil

  (* type hip_args = { *)
  (*   tp: TP.tp_type; *)
  (*   eps: bool; *)
  (*   eap: bool; *)
  (*   esn: bool; *)
  (*   esi: bool; *)
  (*   efp: bool; *)
  (*   cache: bool; *)
  (*   increm: bool; *)
  (* } *)

  let infile = "hip.in." ^ (string_of_int (Unix.getpid ()))
  let outfile = "hip.out." ^ (string_of_int (Unix.getpid ()))
  let errfile = "hip.err." ^ (string_of_int (Unix.getpid ()))

  let debug_log_buffer = Buffer.create 1024
  let prover_log_buffer = Buffer.create 1024
  let console_log_buffer = Buffer.create 1024
  let error_positions = ref ([]: seg_pos list)

  (* let default_args = { *)
  (*   tp = TP.OmegaCalc; *)
  (*   eps = false; *)
  (*   eap = false; *)
  (*   esn = false; *)
  (*   esi = false; *)
  (*   efp = false; *)
  (*   cache = true; *)
  (*   increm = false; *)
  (* } *)

  (* let build_args_string (args: hip_args) = *)
  (*   let tp_name = TP.string_of_tp args.tp in *)
  (*   let tp = "-tp " ^ tp_name in *)
  (*   let log = " --log-" ^ tp_name in *)
  (*   let eps = if args.eps then " --eps" else "" in *)
  (*   let eap = if args.eap then " --eap" else "" in *)
  (*   let esn = if args.esn then " --esn" else "" in *)
  (*   let esi = if args.esi then " --esi" else "" in *)
  (*   let efp = if args.efp then " --efp" else "" in *)
  (*   let cache = if not args.cache then " --no-cache" else "" in *)
  (*   let increm = if args.increm then " --increm" else "" in *)
  (*   let res = tp ^ log ^ eps ^ eap ^ esn ^ esi ^ efp ^ cache ^ increm in *)
  (*   res *)

  (* let hip_command (args: hip_args) (proc_name: string) = *)
  (*   let args = build_args_string args in *)
  (*   Printf.sprintf "./hip -dd %s -p %s %s>%s 2>%s" args proc_name infile outfile errfile *)

  (** run hip with source text and return result string *)
  (* let run_hip ?(args = default_args) (src: string) (proc_name: string) = *)
  (*   FileUtil.write_to_file infile src; *)
  (*   let cmd = hip_command args proc_name in *)
  (*   log ("Executing: " ^ cmd); *)
  (*   ignore (Sys.command cmd); *)
  (*   let res = FileUtil.read_from_file outfile in *)
  (*   (\* save log messages for later use *\) *)
  (*   Buffer.clear debug_log_buffer; *)
  (*   Buffer.add_string debug_log_buffer (FileUtil.read_from_file errfile); *)
  (*   Buffer.clear prover_log_buffer; *)
  (*   let tp_log_file = TP.log_file_of_tp args.tp in *)
  (*   Buffer.add_string prover_log_buffer (FileUtil.read_from_file tp_log_file); *)
  (*   Buffer.clear console_log_buffer; *)
  (*   Buffer.add_string console_log_buffer (FileUtil.read_from_file outfile); *)
  (*   (\* remove temp files *\) *)
  (*   Sys.remove infile; *)
  (*   Sys.remove outfile; *)
  (*   Sys.remove errfile; *)
  (*   (\* return output *\) *)
  (*   res *)

let get_cprog fname= MU.pre_process_source_full fname

let run_hip_from_file_x ocprog (proc_name: string) =
  (* let _ = Scriptarguments.set_proc_verified proc_name in *)
   (* let ocprog = MU.pre_process_source_full src in *)
  match ocprog with
  | None -> true, None
  | Some cprog ->
      (* let procs = CA.list_of_procs cprog in *)
      (* let pr = Gen.Basic.pr_list (fun x -> x.CA.proc_name) in *)
      (* let _= print_endline ("procs: " ^ (pr procs) ) in *)
      let proc = CA.find_proc cprog proc_name in
  (* let procs = Gen.split_by "," proc_name in *)
  (*   Globals.procs_verified := procs; *)
      let res =
        try
        (* let _ = MU.process_source_full src in *)
        (* true *)
            let r, np = TC.check_proc cprog proc in (r, Some np)
        with _ -> (false, Some proc)
      in res

let run_hip_from_file cprog (proc_name: string) =
  let pr1 x = x in
  let pr2 = fun (b,_) -> string_of_bool b in
  Debug.ho_1 "run_hip_from_file" pr1 pr2
      (fun _ -> run_hip_from_file_x cprog proc_name) proc_name

let run_hip_from_txt_x (txt: string) (proc_name: string) =
  FileUtil.write_to_file infile txt;
  let _,ocprog = MU.pre_process_source_full infile in
  let res = run_hip_from_file ocprog txt in
  Sys.remove infile;
  Sys.remove outfile;
  Sys.remove errfile;
  res

let run_hip_from_txt cprog (proc_name: string) =
  let pr1 x = x in
  let pr2 = fun (x,_) -> string_of_bool x in
  Debug.ho_1 "run_hip_from_txt" pr1 pr2
      (fun _ -> run_hip_from_txt_x cprog proc_name) proc_name

  (* let parse_locs_line (line: string) : seg_pos list = *)
  (*   let parse loc = *)
  (*     let regexp = Str.regexp "(\\([0-9]+\\)-\\([0-9]+\\))" in *)
  (*     let _ = Str.string_match regexp loc 0 in *)
  (*     { start_char = int_of_string (Str.matched_group 1 loc); *)
  (*       stop_char = int_of_string (Str.matched_group 2 loc); *)
  (*       start_line = 0; (\* ignore for now *\) *)
  (*       stop_line = 0; (\* ignore for now *\) *)
  (*     } *)
  (*   in *)
  (*   let locs = Str.split (Str.regexp ",") line in *)
  (*   List.map parse locs *)

  (* let parse_result (hip_output: string) = *)
  (*   let err_pos =  *)
  (*     try *)
  (*       let regexp = Str.regexp "Possible locations of failures: \\([^\\.]+\\)\\." in *)
  (*       let _ = Str.search_forward regexp hip_output 0 in *)
  (*       let locs_line = Str.matched_group 1 hip_output in *)
  (*       log ("Failed branches location: " ^ locs_line); *)
  (*       parse_locs_line locs_line; *)
  (*     with Not_found -> [] *)
  (*   in *)
  (*   error_positions := err_pos; *)
  (*   let regexp = Str.regexp_string "SUCCESS" in *)
  (*   let res =  *)
  (*     try *)
  (*       ignore (Str.search_forward regexp hip_output 0); *)
  (*       log "Success."; *)
  (*       true *)
  (*     with Not_found -> (log "FAIL!"; false) *)
  (*   in *)
  (*   res *)

 let check_proc_from_file ocprog (p: procedure) =
    let res = run_hip_from_file ocprog p.mname in
    res
    (* parse_result res *)

let check_proc_from_txt (txt: string) (p: procedure) =
    let res = run_hip_from_txt txt p.mname in
    res
    (* parse_result res *)

  let get_debug_log () = Buffer.contents debug_log_buffer

  let get_prover_log () = Buffer.contents prover_log_buffer

  let get_console_log () = Buffer.contents console_log_buffer

  let get_error_positions () = !error_positions

  let rec cmb_join_branches ll (m1, oft1)=
    match ll with
      | [] -> (m1, oft1)
      | (m2, oft2)::xs ->
          let n_msg, oft=
            match oft1, oft2 with
              | Some ft1, Some ft2 -> m1 ^ "\nJoin\n" ^ m2,
                  Some (Cformula.Or_Reason (ft1,ft2))
              | Some _, None -> m1, oft1
              | None, Some _ -> m2, oft2
              | None, None -> m1, None
          in (cmb_join_branches xs (n_msg,  oft))

end (* HipHelper *)


(** List of recent documents opened by gHip *)
module RecentDocuments = struct

  let home_dir = Sys.getenv "HOME"
  let history_file = home_dir ^ "/.hip_recent"

  let get_recent_documents ?(limit=0) () =
    let rec nhd n lst =
      (* return first n items of a list, n must be less than length of the list *)
      if n = 0 then []
      else (List.hd lst)::(nhd (n-1) (List.tl lst))
    in
    if Sys.file_exists history_file then
      let file_content = FileUtil.read_from_file history_file in
      let lines = Str.split (Str.regexp "\n") file_content in
      let res = 
        if List.length lines < limit || limit = 0 then lines 
        else nhd limit lines in
      res
    else []

  let rec string_join (delim: string) (eles: string list) =
    match eles with
    | [] -> ""
    | [e] -> e
    | e::rest -> e ^ delim ^ (string_join delim eles)

  let add_to_recent_documents (fname: string) =
    let current = get_recent_documents () in
    let filtered = List.filter (fun x -> x <> fname) current in
    let new_list = fname::filtered in
    let text = string_join "\n" new_list in
    FileUtil.write_to_file history_file text

end (* RecentDocuments *)
