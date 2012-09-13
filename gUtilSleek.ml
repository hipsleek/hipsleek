open Globals
open GUtil

(**/**)
module TP = Tpdispatcher
module SE = Sleekengine
module SC = Sleekcommons
module FU = FileUtil
(**/**)
module M = Lexer.Make(Token.Token)

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
    try
        let lexbuf = Stream.of_string src in
        Parser.parse_sleek "editor_buffer" lexbuf
    (* let lexbuf = Lexing.from_string src in
    Sparser.opt_command_list (Slexer.tokenizer "editor_buffer") lexbuf*)
    with
	  | End_of_file ->
		  print_string ("\n"); []
      | M.Loc.Exc_located (l,t)-> 
          (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
           raise t)

(*  let process_cmd_line () = Arg.parse Scriptarguments.sleek_arguments SC.set_source_file SC.usage_msg*)

  let process_cmd cmd:(string*string) =
    begin
        (*log ("process command: " ^ (String.concat "\n" (List.map SC.string_of_command cmds)));*)
        log ("process command: " ^ SC.string_of_command cmd);
    (*  process_cmd_line ();*)
        Tpdispatcher.start_prover ();
        Gen.Profiling.push_time "Overall";
        let res = ("","")
          (* Sleekengine.process_cmd_with_string cmd *) in
        Gen.Profiling.pop_time "Overall";
        Tpdispatcher.stop_prover ();
        res
    end

(*
    match cmd with
    | SC.DataDef (ddef,_) ->
        log "processing data def";
        SE.process_data_def ddef; None
    | SC.PredDef (pdef,_) ->
        log "processing pred def";
        SE.process_pred_def pdef; None
    | SC.EntailCheck (iante, iconseq,_) ->
        log "processing entail check";
        Some (SE.run_entail_check iante iconseq)
    | SC.CaptureResidue (lvar,_) ->
        log "processing capture residue";
        SE.process_capture_residue lvar; None
    | SC.LemmaDef (ldef,_) ->
        log "processing lemmad def";
        SE.process_lemma ldef; None
    | SC.PrintCmd (pcmd,_) ->
        log "processing print cmd";
        SE.process_print_command pcmd; None
    | SC.LetDef (lvar, lbody,_) ->
        log "processing let def";
        SC.put_var lvar lbody; None
    | SC.Time (b,s,_) -> None
    | SC.EmptyCmd -> None
*)
(*
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
*)
end (* SleekHelper *)

class step_info =

object (self)
  val mutable pos = no_pos
  val mutable id = -1
  val mutable name = ""
  (*lhs/rhs/es*)

  method set i p n=
    id <- i;
    pos <- p;
    name <- n

  method get_id = id

  method get_name = name

  method get_pos = pos

end

class cmd_info =

object (self)
  val mutable cmd = SC.EmptyCmd (*kind of cmd*)
  val mutable pos = -1 (*start line number in file*)
  val mutable steps = ([]: step_info list) (*Hashtbl.create 512*)
  val mutable cur_step = -1 (*current step*)

  (*methods*)
  method set_init c p =
    cmd <- c;
    pos <- p;
    cur_step <- 1

  method set_all c p cs ss=
    cmd <- c;
    pos <- p;
    cur_step <- cs;
    steps <- ss

  method get = (cmd,pos)

  method get_cmd = cmd

  method get_current_step = cur_step

  method get_steps():(step_info list) = steps

  method get_pos = SC.pos_of_command cmd

  method string_of_cmd():string= (SC.string_of_command cmd) ^" at "^(string_of_int pos) ^ "#" ^ (string_of_int cur_step)

  method reset ()=
    cmd <- SC.EmptyCmd;
    pos <- -1;
    steps <- [];
    cur_step <- -1;
    ()

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

class sleek_file_info =

object (self)
  val mutable file_name = ""
  val mutable current_line_pos = -1 (*line number*)
  val mutable total_line = 0
  val mutable current_cmd_idx = (-1:int) (*the order in cmd*)
  (*val cmds = Hashtbl.create 128*)
  val mutable cmds = ([] : cmd_info list)
  val mutable decl_cmds = ([] : cmd_info list)
  val mutable lines_pos = ([]: (int*int) list) (*mapping from line number -> begin char, end char*)

  method set addr p n=
    file_name <- addr;
    current_line_pos <- p;
    total_line <- n

  method set_current_line_pos p = current_line_pos <- p

   method set_current_cmd cmd_idx = current_cmd_idx <- cmd_idx

  method get_file_name = file_name

  method get_current_line_pos = current_line_pos

  method get_current_cmd_idx = current_cmd_idx

  method get_list_cmds():(cmd_info list) =
    (*Hashtbl.fold (fun a b ls-> b::ls) cmds []*)
    cmds

  method get_decl_cmds():(cmd_info list) =
    (*Hashtbl.fold (fun a b ls-> b::ls) cmds []*)
    decl_cmds

  method get_total_line = total_line

  method get_lines_map = lines_pos

  method private get_cmds_size():int= List.length cmds

  method private get_current_cmd():cmd_info = List.nth cmds current_cmd_idx

  method private build_cmds cmds:(cmd_info list)=
    let helper cmd:cmd_info=
      let pos = SC.pos_of_command cmd in
      let lnum = SourceUtil.get_line_num pos in
      let c = new cmd_info in
        c#set_init cmd lnum;
      c
    in List.map helper cmds

  (*return current pos + src*)
  method load_new_file (fname:string):(int*string)=
    (*reset old content*)
    let _ = SE.clear_all () in
    (*inbuilt data*)
    wrap_exists_implicit_explicit := false ;
    let _ = SE.main_init() in

    (*load file, src = file contend*)
    let src = FU.read_from_file fname in
    (*let cmds = parse_all src*)
    let ls_cmds = SleekHelper.parse_command_list src in
    (*parse lines position in src*)
    lines_pos <- (SourceUtil.get_lines_positions src);
    total_line <- List.length lines_pos;
    (*let _ = print_endline (SourceUtil.string_of_lines lines_pos) in*)
    (*add all cmds into cmds*)
    let cmds1, cmds2 = List.partition SE.is_decl_cmd ls_cmds in
    let cmds12 = self#build_cmds cmds1 in
    decl_cmds <- cmds12 ;
    let cmds22 = self#build_cmds cmds2 in
    cmds <- cmds22;
    file_name <- fname;
    (*set current line = first line of text; current cmd = first cmd*)
    current_cmd_idx <- 0;
    let temp = List.nth cmds current_cmd_idx in
    (*let _ = print_endline (current_cmd#string_of_cmd()) in*)
    current_line_pos <- SourceUtil.get_line_num temp#get_pos;
    (*let _ = print_endline (string_of_int current_line_pos) in*)
    (current_line_pos,src)

  (*return current pos + src*)
  method create_new_file ():(int*string)=
   begin
    file_name <- "";
    current_line_pos <- 1;
    total_line <- 0;
    current_cmd_idx<-0;

    (current_line_pos,"")
   end

  method move_next_step (p:int)=
   (*res = new pos, new cmd*)

  ()

  method move_prev_step (p:int)=
   (*res = new pos, new cmd*)

  ()

  (*return ctx*prf *)
  method process_remain_current_cmd():(string*string)=
    (*run remain of entailemt process*)
     let temp = self#get_current_cmd () in
     let slk_cmd = temp#get_cmd in
     SleekHelper.process_cmd slk_cmd

  method process_cmd(c:cmd_info):(string*string)=
     let slk_cmd = c#get_cmd in
     SleekHelper.process_cmd slk_cmd

  method process_cmds (cmds:cmd_info list):(string*string)=
    let (ls, prf) = List.split (List.map self#process_cmd cmds) in
    (String.concat "\n" ls, String.concat "\n" prf)

  method move_to_next_cmd ():int=
   (*res = new pos, new cmd*)
    if current_cmd_idx < (self#get_cmds_size()-1) then
      begin
          current_cmd_idx <- current_cmd_idx + 1;
    (*let _ = print_endline (current_cmd#string_of_cmd()) in*)
          let temp = self#get_current_cmd() in
          current_line_pos <- SourceUtil.get_line_num temp#get_pos;
          current_line_pos
      end
    else
      current_line_pos

  method back_to_prev_cmd():int=
   (*res = new pos, new cmd*)
    if current_cmd_idx > 0 then
      begin
          current_cmd_idx <- current_cmd_idx - 1;
          let temp = self#get_current_cmd () in
    (*let _ = print_endline (current_cmd#string_of_cmd()) in*)
          current_line_pos <- SourceUtil.get_line_num temp#get_pos;
          current_line_pos
      end
    else
      current_line_pos

  method move_to_current_point (p:int)=

  ()

  method get_proofs (cmd:cmd_info)=
   true

end
