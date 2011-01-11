module TP = Tpdispatcher

let create_scrolled_win child = 
  let scroll_win = GBin.scrolled_window 
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC 
    () in
  scroll_win#add child#coerce;
  scroll_win

(**********************************
 * Common operations on text file
 **********************************)
module FileUtil = struct

  (* read a text file and then return it's content as a string *)
  let read_from_file (fname: string) : string =
    let ic = open_in fname in
    let size = in_channel_length ic in
    let buf = String.create size in
    really_input ic buf 0 size;
    close_in ic;
    buf

  (* write text to a file (with name fname *)
  let write_to_file (fname: string) (text: string) : unit =
    let oc = open_out fname in
    output_string oc text;
    flush oc;
    close_out oc;
    ()

end (* FileUtil *)


(************************************************
 * Quick & dirty parsing functions of sleek file
 * based on simple regular expressions
 ************************************************)
module SourceUtil = struct

  type entailment = {
    formula: string; (* the entailment formula *)
    start_char: int;
    start_line: int;
    stop_char: int;
    stop_line: int;
  }
  type substring_pos = {
    start: int;
    stop: int;
  }
  type position = GText.position

  let checkentail_re = Str.regexp "checkentail \\([^\\.]+\\)\\."
  let print_re = Str.regexp "print [^\\.]+\\."
  let new_line_re = Str.regexp "^"

  (* return a list of all positions of "new line" char in src *)
  let get_new_line_positions (src: string) : int list =
    let rec new_line_pos (start: int): int list =
      try
        let pos = Str.search_forward new_line_re src start in
        pos::(new_line_pos (pos+1))
      with Not_found | Invalid_argument _ -> []
    in
    new_line_pos 0

  (* map a position to it's line number
   * based on a list of positions of new line chars *)
  let char_pos_to_line_num (pos: int) (new_lines: int list) : int =
    (* return index of first item in list xs which value greater than x
     * return -1 if xs is empty *)
    let rec greater_than x xs = match xs with
      | [] -> -1
      | head::tail -> if head > x then 0 else 1+(greater_than x tail)
    in
    greater_than pos new_lines

  (* remove all checkentail command from source *)
  let remove_checkentail (src: string) : string =
    Str.global_replace checkentail_re "" src

  (* remove all print command from source *)
  let remove_print (src: string) : string =
    Str.global_replace print_re "" src

  let clean (src: string) : string =
    let res = remove_checkentail src in
    let res = remove_print res in
    res

  (* parse sleek file and return list of entailments (to be checked) *)
  let parse_entailment_list (src: string) : entailment list =
    let new_lines = get_new_line_positions src in
    let to_line_num pos = char_pos_to_line_num pos new_lines in
    let rec parse (start: int) : entailment list =
      try
        let start_char = Str.search_forward checkentail_re src start in
        let stop_char = Str.match_end () in
        let f = Str.matched_group 1 src in
        let start_line = to_line_num start_char in
        let stop_line = to_line_num stop_char in
        let first = {
          start_char = start_char;
          stop_char = stop_char;
          start_line = start_line;
          stop_line = stop_line;
          formula = f;
        } in
        first::(parse (stop_char+1))
      with Not_found -> []
    in
    parse 0

  let search (doc: string) (substring: string) : substring_pos list =
    let reg = Str.regexp_string substring in
    let rec search_next (start: int) : substring_pos list =
      try
        let start_char = Str.search_forward reg doc start in
        let stop_char = Str.match_end () in
        let pos = { start = start_char; stop = stop_char} in
        pos::(search_next (stop_char+1))
      with Not_found -> []
    in
    search_next 0

(*
 *  let parse_command_list (src: string) =
 *    let lexbuf = Lexing.from_string src in
 *    Sparser.opt_command_list (Slexer.tokenizer "editor_buffer") lexbuf
 *
 *  let exec_nth_checkentail_cmd (src: string) (n: int) : bool =
 *    let _ = SE.reset_data () in
 *    let cmd_list = parse_command_list src in
 *    let rec exec_nth cmd_list count = match cmd_list with
 *      | [] -> invalid_arg "[gsleek.ml/exec_nth_checkentail_cmd]:nth"
 *      | head::rest ->
 *          let p = SE.process_cmd head (count = n) in
 *          let res = match p with
 *            | Some r -> r
 *            | None ->
 *                if SC.is_entailcheck_cmd head then
 *                  exec_nth rest (count+1)
 *                else
 *                  exec_nth rest count
 *          in res
 *    in
 *    exec_nth cmd_list 0
 *)

end (* SourceUtil *)


(**********************************************
 * Helper for interacting with Sleek script
 * Command calling, process management, parsing of result,...
 **********************************)
module SleekHelper = struct

  module SU = SourceUtil

  type sleek_args = {
    tp: TP.tp_type;
    eps: bool;
    eap: bool;
  }

  let infile = "/tmp/sleek.in." ^ (string_of_int (Unix.getpid ()))
  let outfile = "/tmp/sleek.out." ^ (string_of_int (Unix.getpid ()))
  let errfile = "/tmp/sleek.err." ^ (string_of_int (Unix.getpid ()))

  let default_args = {
    tp = TP.OmegaCalc;
    eps = false;
    eap = false;
  }

  let build_args_string (args: sleek_args) =
    let tp = " -tp " ^ (TP.string_of_tp args.tp) in
    let eps = if args.eps then " --eps" else "" in
    let eap = if args.eap then " --eap" else "" in
    let res = tp ^ eps ^ eap in
    res

  let sleek_command (args: sleek_args) = 
    let args_string = build_args_string args in
    Printf.sprintf "./sleek -dd %s %s > %s 2> %s" args_string infile outfile errfile

  (* run sleek with source text and return result string *)
  let run_sleek ?(args = default_args) (src: string) =
    FileUtil.write_to_file infile src;
    let cmd = sleek_command args in
    ignore (Sys.command cmd);
    let res = FileUtil.read_from_file outfile in
    let log = FileUtil.read_from_file errfile in
    Sys.remove infile;
    Sys.remove outfile;
    Sys.remove errfile;
    res, log

  let parse_checkentail_result (res: string) =
    let regexp = Str.regexp "Valid\\." in
    try
      ignore (Str.search_forward regexp res 0);
      true
    with Not_found -> false

  let checkentail ?args (src: string) (e: SU.entailment) =
    let header = SU.clean (String.sub src 0 e.SU.start_char) in
    let src = Printf.sprintf "%s checkentail %s. print residue." header e.SU.formula in
    let res, log = run_sleek ?args src in
    parse_checkentail_result res, res, log
    
end (* SleekHelper *)

