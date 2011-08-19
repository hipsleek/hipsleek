open Globals
open GUtil

(**/**)
module TP = Tpdispatcher
module SE = Sleekengine
module SC = Sleekcommons
(**/**)

class step_info =

object (self)
  val mutable pos = no_pos
  val mutable id = -1
  val mutable name = ""
  (*pre/post/es*)

end

class cmd_info =

object (self)
  val mutable cmd = SC.EmptyCmd (*kind of cmd*)
  val mutable pos = no_pos (*positions of cmd in file*)
  val steps = Hashtbl.create 512
  val mutable int = -1 (*current step*)

  (*methods*)
  method set c p =
    cmd <- c;
    pos <- p

  method get_cmd = cmd

  method get_pos = pos

  method next_step =
  (*check the ability to move forward- entailment is complete or not*)

  (*if current step != -1, get current step. If can not move return a exception*)

  (*call to move one step*)

  (*increase current step number, add new step to hashtbl*)

  (*return new step*)

  ()

  method back_step =
  (*if current step != -1, 0 a exception*)

  (*decrease current step number, extract prev. step from hashtbl*)

  (*return prev. step*)
  ()

  method get_current_proofs=
  (*travel all steps, for each get its name/proof*)

  ()

end
(**
   Helper for interacting with Sleek script
   Command calling, process management, parsing of result,...
 *)
module SleekHelper = struct

  open SourceUtil

  type sleek_args = {
    tp: TP.tp_type;
    eps: bool;
    eap: bool;
    esn: bool;
    esi: bool;
    efp: bool;
    cache: bool;
    increm: bool;
  }

  let infile = "/tmp/sleek.in." ^ (string_of_int (Unix.getpid ()))
  let outfile = "/tmp/sleek.out." ^ (string_of_int (Unix.getpid ()))

  let default_args = {
    tp = TP.OmegaCalc;
    eps = false;
    eap = false;
    esn = false;
    esi = false;
    efp = false;
    cache = true;
    increm = false;
  }

  let string_of_entailment (e: entailment) =
    Printf.sprintf "(%d,%d): %s" e.pos.start_line e.pos.stop_line e.name


  let build_args_string (args: sleek_args) =
    let tp = " -tp " ^ (TP.string_of_tp args.tp) in
    let eps = if args.eps then " --eps" else "" in
    let eap = if args.eap then " --eap" else "" in
    let esn = if args.esn then " --esn" else "" in
    let esi = if args.esi then " --esi" else "" in
    let efp = if args.efp then " --efp" else "" in
    let cache = if not args.cache then " --no-cache" else "" in
    let increm = if args.increm then " --increm" else "" in
    let res = tp ^ eps ^ eap ^ esn ^ esi ^ efp ^ cache ^ increm in
    res

  let sleek_command (args: sleek_args) = 
    let args_string = build_args_string args in
    Printf.sprintf "./sleek -dd %s %s > %s" args_string infile outfile

  (** run sleek with source text and return result string *)
  let run_sleek ?(args = default_args) (src: string) =
    FileUtil.write_to_file infile src;
    let cmd = sleek_command args in
    ignore (Sys.command cmd);
    let res = FileUtil.read_from_file outfile in
    Sys.remove infile;
    Sys.remove outfile;
    res

  let parse_checkentail_result (res: string) =
    let regexp = Str.regexp "Valid\\." in
    try
      ignore (Str.search_forward regexp res 0);
      true
    with Not_found -> false

  let checkentail_external ?args (src: string) (e: entailment) =
    let header = clean (String.sub src 0 e.pos.start_char) in
    let src = Printf.sprintf "%s checkentail %s. print residue." header e.name in
    let res = run_sleek ?args src in
    parse_checkentail_result res, res

  let parse_command_list (src: string) : SC.command list =
    let lexbuf = Stream.of_string src in
    Parser.parse_sleek "editor_buffer" lexbuf
    (* let lexbuf = Lexing.from_string src in
    Sparser.opt_command_list (Slexer.tokenizer "editor_buffer") lexbuf*)

  let process_cmd cmd = match cmd with
    | SC.DataDef ddef -> 
        log "processing data def";
        SE.process_data_def ddef; None
    | SC.PredDef pdef -> 
        log "processing pred def";
        SE.process_pred_def pdef; None
    | SC.EntailCheck (iante, iconseq) -> 
        log "processing entail check"; 
        Some (SE.run_entail_check iante iconseq)
    | SC.CaptureResidue lvar -> 
        log "processing capture residue";
        SE.process_capture_residue lvar; None
    | SC.LemmaDef ldef -> 
        log "processing lemmad def";
        SE.process_lemma ldef; None
    | SC.PrintCmd pcmd -> 
        log "processing print cmd";
        SE.process_print_command pcmd; None
    | SC.LetDef (lvar, lbody) -> 
        log "processing let def";
        SC.put_var lvar lbody; None
    | SC.Time (b,s,_) -> None
    | SC.EmptyCmd -> None

  let checkentail src e =
    try
      log ("Checking entailment: " ^ (string_of_entailment e));
      let header = clean (String.sub src 0 e.pos.start_char) in
      let src = Printf.sprintf "%s checkentail %s." header e.name in
      let cmds = parse_command_list src in
      let _ = SE.clear_all () in
      let rec exec cmds = match cmds with
        | [] -> failwith "[gUtil.ml/checkentail]: empty command list"
        | [cmd] -> process_cmd cmd
        | cmd::rest -> ignore (process_cmd cmd); exec rest
      in
      let res, contexts = match exec cmds with
        | None -> failwith "[gUtil.ml/checkentail]: last command is not checkentail command"
        | Some v -> v
      in
      let residue = match SE.get_residue () with
        | Some residue ->
            let formulas = Cformula.list_formula_of_list_context residue in
            let fstring = Cprinter.string_of_list_formula formulas in
            "Residue:\n" ^ fstring ^ "\n"
        | None -> ""
      in
      let context = Cprinter.string_of_list_context contexts in
      let info = residue ^ context in
      let valid = if res then "valid" else "fail" in
      log valid;
      res, info
    with exn as e ->
      false, (Printexc.to_string e) ^ "\n" ^ (Printexc.get_backtrace ())

end (* SleekHelper *)
