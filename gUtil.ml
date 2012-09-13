(**
   Helper and other ultilities for Hip/Sleek's GUI
 *)

open Globals

(**/**)
module TP = Tpdispatcher
module SE = Sleekengine
module SC = Sleekcommons
(**/**)

(** Wrap a widget in a scrolled window and return that window
 *)
let create_scrolled_win child = 
  let scroll_win = GBin.scrolled_window 
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC 
    () in
  scroll_win#add child#coerce;
  scroll_win

(**/**)
let log_func = ref (fun _ -> raise Not_found)
let verbose_flag = ref true
(**/**)
(** Print msg to stdout if verbose flag is on *)
let log msg =
  if !verbose_flag then begin
    try !log_func msg
    with Not_found ->
      log_func := (fun msg -> print_endline msg; flush stdout);
      !log_func msg
  end

(**
   Common operations on text file
 *)
module FileUtil = struct

  (** Read a text file and then return it's content as a string 
   *)
  let read_from_file (fname: string) : string =
    if Sys.file_exists fname then begin
      let ic = open_in fname in
      let size = in_channel_length ic in
      let buf = String.create size in
      really_input ic buf 0 size;
      close_in ic;
      buf
    end else ""

  (** Write text to a file 
   *)
  let write_to_file (fname: string) (text: string) : unit =
    let oc = open_out fname in
    output_string oc text;
    flush oc;
    close_out oc;
    ()

end (* FileUtil *)


(**
   Quick & dirty parsing functions of sleek file
   based on simple regular expressions
   TODO: use sleek parser for parsing
 *)
module SourceUtil = struct

   type seg_pos = {
    start_char: int;
    start_line: int;
    stop_char: int;
    stop_line: int;
  }

  type procedure = {
    name: string;
    mname: string;
    pos: seg_pos;
  }

  type entailment = procedure

  exception Syntax_error of string * seg_pos

  let checkentail_re = Str.regexp "checkentail \\([^\\.]+\\)\\."

  let string_of_seg_pos pos =
    Printf.sprintf "(%d-%d, line %d-%d)" 
      pos.start_char pos.stop_char
      pos.start_line pos.stop_line

  (** return a list of all positions of "new line" char in src *)
  let get_new_line_positions (src: string) : int list =
    let new_line_re = Str.regexp "^" in
    let rec new_line_pos (start: int): int list =
      try
        let pos = Str.search_forward new_line_re src start in
        pos::(new_line_pos (pos+1))
      with Not_found | Invalid_argument _ -> []
    in
    new_line_pos 1

  (** return a map of all line in src *)
  let get_lines_positions (src: string) : (int*int) list =
    let new_line_re = Str.regexp "^" in
    let rec new_line_pos (start: int): (int*int) list =
      try
        let pos = Str.search_forward new_line_re src start in
        (start, pos)::(new_line_pos (pos+1))
      with Not_found | Invalid_argument _ -> []
    in
    (new_line_pos 0)

  let get_line_pos lnum m=
   List.nth m lnum

  let get_line_num (p:loc):int= p.start_pos.Lexing.pos_lnum

  let string_of_line_pos lnum m=
    let(s,e) = List.nth m lnum in
    ("line " ^ (string_of_int lnum)^ ":" ^ (string_of_int s)^"->" ^ (string_of_int e))

  let string_of_lines m=
    let rec helper l all_lines=
      match all_lines with
        | [] -> ""
        | (s,e)::xs -> ("line " ^ (string_of_int l)^ ":" ^ (string_of_int s)^"->" ^ (string_of_int e)
          ^ "\n") ^ (helper (l+1) xs)
    in helper 0 m

  (** map a position to it's line number,
     based on a list of positions of new line chars
   *)
  let char_pos_to_line_num (pos: int) (new_lines: int list) : int =
    (** return index of first item in list xs which value greater than x
       return -1 if xs is empty *)
    let rec greater_than x xs = match xs with
      | [] -> -1
      | head::tail -> if head > x then 0 else 1+(greater_than x tail)
    in
    greater_than pos new_lines

  (** remove all checkentail command from source *)
  let remove_checkentail (src: string) : string =
    Str.global_replace checkentail_re "" src

  (** remove all print command from source *)
  let remove_print (src: string) : string =
    let print_re = Str.regexp "print [^\\.]+\\." in
    Str.global_replace print_re "" src

  let clean (src: string) : string =
    let res = remove_checkentail src in
    let res = remove_print res in
    res

  (** parse sleek file and return list of entailments (to be checked) *)
  let parse_entailment_list (src: string) : entailment list =
    let new_lines = get_new_line_positions src in
    let to_line_num pos = char_pos_to_line_num pos new_lines in
    let rec parse_e (start: int) : entailment list =
      try
        let start_char = Str.search_forward checkentail_re src start in
        let stop_char = Str.match_end () in
        let f = Str.matched_group 1 src in
        let start_line = to_line_num start_char in
        let stop_line = to_line_num stop_char in
        let pos = {
          start_char = start_char;
          stop_char = stop_char;
          start_line = start_line;
          stop_line = stop_line;
        } in
        let first = {
          pos = pos;
          mname = f;
          name = f;
        } in
        first::(parse_e (stop_char+1))
      with Not_found -> []
    in
    parse_e 0

  let parse_procedure_list (src: string) : procedure list =
    let parse (proc: Iast.proc_decl) : procedure =
      let proc_pos = proc.Iast.proc_loc in
      let pos = {
        start_char = proc_pos.start_pos.Lexing.pos_cnum;
        start_line = proc_pos.start_pos.Lexing.pos_lnum;
        stop_char = proc_pos.end_pos.Lexing.pos_cnum;
        stop_line = proc_pos.end_pos.Lexing.pos_lnum;
      } in
      {
        name = proc.Iast.proc_name;
        mname = Cast.mingle_name proc.Iast.proc_name (List.map (fun p -> p.Iast.param_type) proc.Iast.proc_args);
        pos = pos;
      }
    in
    let lexbuf = Lexing.from_string src in
    try
      (*let prog = Iparser.program (Ilexer.tokenizer "editor_buffer") lexbuf in*)
      let prog = Parser.parse_hip "editor_buffer" (Stream.of_string src) in
      let procs = prog.Iast.prog_proc_decls in
      List.rev_map parse procs
    with Parsing.Parse_error ->
      let start_p = lexbuf.Lexing.lex_start_p in
      let curr_p = lexbuf.Lexing.lex_curr_p in
      let pos = {
        start_char = start_p.Lexing.pos_cnum;
        stop_char = curr_p.Lexing.pos_cnum;
        start_line = start_p.Lexing.pos_lnum;
        stop_line = curr_p.Lexing.pos_lnum;
      } in
      log (Printf.sprintf "Syntax error at line %d" start_p.Lexing.pos_lnum);
      raise (Syntax_error ("Syntax error!", pos))

let get_procedure_list (procs: Iast.proc_decl list) : procedure list =
    let parse (proc: Iast.proc_decl) : procedure =
      let proc_pos = proc.Iast.proc_loc in
      let pos = {
        start_char = proc_pos.start_pos.Lexing.pos_cnum;
        start_line = proc_pos.start_pos.Lexing.pos_lnum;
        stop_char = proc_pos.end_pos.Lexing.pos_cnum;
        stop_line = proc_pos.end_pos.Lexing.pos_lnum;
      } in
      {
        name = proc.Iast.proc_name;
        mname = Cast.mingle_name proc.Iast.proc_name (List.map (fun p -> p.Iast.param_type) proc.Iast.proc_args);
        pos = pos;
      }
    in
    List.rev_map parse procs

  (** search for all substring in a string *)
  let search (doc: string) (sub: string) : seg_pos list =
    let reg = Str.regexp_string sub in
    let rec search_next (start: int) : seg_pos list =
      try
        let start_char = Str.search_forward reg doc start in
        let stop_char = Str.match_end () in
        let pos = { 
          start_char = start_char; stop_char = stop_char;
          start_line = -1; stop_line = -1
        } in
        pos::(search_next (stop_char+1))
      with Not_found -> []
    in
    search_next 0

end (* SourceUtil *)


let initialize () =
  ignore (GtkMain.Main.init ());
  Debug.devel_debug_on := true;
  Debug.log_devel_debug := true;
(*
  Globals.reporter := (fun loc msg ->
    let pos = {
      SourceUtil.start_char = loc.start_pos.Lexing.pos_cnum;
      SourceUtil.stop_char = loc.end_pos.Lexing.pos_cnum;
      SourceUtil.start_line = loc.start_pos.Lexing.pos_lnum;
      SourceUtil.stop_line = loc.end_pos.Lexing.pos_lnum;
    } in
    raise (SourceUtil.Syntax_error ("Syntax error: " ^ msg ^ "!", pos))
  );
*)
  (*TP.enable_log_for_all_provers ();*)
  (*TP.start_prover*) ()

(* let finalize () = *)
(*   TP.stop_prover() *)
