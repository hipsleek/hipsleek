(*************************
 * GUI frontend for Sleek
 *************************)

module SC = Sleekcommons
module SE = Sleekengine

(**********************************
 * Operations on file
 * (should be in a separated file)
 **********************************)
module FileUtils = struct

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

end (* FileUtils *)


(************************************************
 * Quick & dirty parsing functions of sleek file
 * based on simple regular expressions
 * (should be in a separated file)
 ************************************************)
module SourceUtils = struct

  type entailment = {
    formula: string; (* the entailment formula *)
    start_char: int;
    start_line: int;
    stop_char: int;
    stop_line: int;
  }

  let checkentail_re = Str.regexp "checkentail \\([^\\.]+\\)\\."
  let print_re = Str.regexp "print [^\\.]+\\."
  let new_line_re = Str.regexp "^"

  (* return a list of all positions of "new line" char in src *)
  let new_line_position (src: string) : int list =
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
    let new_lines = new_line_position src in
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
        first::(parse (first.stop_char+1))
      with Not_found -> []
    in
    parse 0

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

end (* SourceUtils *)

open SourceUtils

module SleekHelper = struct

  let infile = "/tmp/sleek.in." ^ (string_of_int (Unix.getpid ()))
  let outfile = "/tmp/sleek.out." ^ (string_of_int (Unix.getpid ()))
  let sleek_command = Printf.sprintf "./sleek %s > %s" infile outfile

  (* run sleek with source text and return result string *)
  let run_sleek (src: string) : string =
    FileUtils.write_to_file infile src;
    ignore (Sys.command sleek_command);
    let res = FileUtils.read_from_file outfile in
    Sys.remove infile;
    Sys.remove outfile;
    res

  let parse_checkentail_result (res: string) : bool =
    let regexp = Str.regexp "Valid\\." in
    try
      ignore (Str.search_forward regexp res 0);
      true
    with Not_found -> false

  let checkentail (src: string) (e: entailment) : bool * string =
    let header = SourceUtils.clean (String.sub src 0 e.start_char) in
    let src = Printf.sprintf "%s checkentail %s. print residue." header e.formula in
    let res = run_sleek src in
    parse_checkentail_result res, res
    
end


(*********************************
 * Entailment list model
 *********************************)
let cols = new GTree.column_list
let col_id = cols#add Gobject.Data.int
let col_line = cols#add Gobject.Data.int
let col_formula = cols#add Gobject.Data.string
let col_validity = cols#add Gobject.Data.string

class entailment_list_model ?source:(src = "") () =
  object (self)
    val delegate = GTree.list_store cols
    val mutable entailment_list = []
    val mutable modified_times = []
    val mutable count = 0

    initializer
      self#update_source src
    
    method coerce = delegate#coerce

    method append_one_entailment (e: entailment) =
      let iter = delegate#append () in
      delegate#set ~row:iter ~column:col_id count;
      delegate#set ~row:iter ~column:col_line e.start_line;
      delegate#set ~row:iter ~column:col_formula e.formula;
      delegate#set ~row:iter ~column:col_validity "gtk-execute";
      count <- count + 1

    method update_source (src: string) =
      delegate#clear ();
      count <- 0;
      entailment_list <- parse_entailment_list src;
      List.iter self#append_one_entailment entailment_list

    method get_entailment_by_path path =
      let row = delegate#get_iter path in
      let id = delegate#get ~row ~column:col_id in
      List.nth entailment_list id

    method set_entaiment_validity path (valid: bool) : unit =
      let row = delegate#get_iter path in
      let stock_id = self#stock_id_of_bool valid in
      delegate#set ~row ~column:col_validity stock_id

    method private stock_id_of_bool b =
      if b then "gtk-apply" else "gtk-cancel"

    method check_all (check_func: entailment -> bool): unit =
      let func path iter =
        let entail = self#get_entailment_by_path path in
        let valid = check_func entail in
        self#set_entaiment_validity path valid;
        false
      in
      delegate#foreach func

  end


(*********************************
 * Entailment list view
 *********************************)
class entailment_list ?model:(model = new entailment_list_model ()) () =
  object (self)
    val view = GTree.view ()
    val mutable model = model
    val validity_col = GTree.view_column
      ~title:"Validity"
      ~renderer:(GTree.cell_renderer_pixbuf [], ["stock_id", col_validity])
      ()

    initializer
      view#selection#set_mode `SINGLE;
      let add_new_col title renderer =
        let col = GTree.view_column ~title ~renderer () in
        col#set_resizable true;
        ignore (view#append_column col);
        col
      in
      let text_renderer = GTree.cell_renderer_text [] in
      ignore (add_new_col "Line" (text_renderer, ["text", col_line]));
      ignore (add_new_col "Entailment" (text_renderer, ["text", col_formula]));
      validity_col#set_resizable true;
      validity_col#set_alignment 0.5;
      validity_col#set_clickable true;
      ignore (view#append_column validity_col);
      view#set_model (Some model#coerce)

    method coerce = view#coerce
    method selection = view#selection

    method set_model new_model =
      model <- new_model;
      view#set_model (Some model#coerce)

    method get_selected_entailment () =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] -> Some (model#get_entailment_by_path row)
      | _ -> None

    method set_selected_entailment_validity valid =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] ->model#set_entaiment_validity row valid
      | _ -> ()

    method check_all (func: entailment -> bool) : unit =
      model#check_all func

    method update_source (src: string) : unit =
      model#update_source src

    method set_checkall_handler callback =
      ignore (validity_col#connect#clicked ~callback)

  end


(***********************
 * Sleek source editor
 ***********************)
class sleek_source_view ?text:(text = "") () =

  let get_sleek_lang () =
    let lang_mime_type = "text/x-sleek" in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    match language_manager#guess_language ~content_type:lang_mime_type () with
    | None -> failwith ("no language for " ^ lang_mime_type)
    | Some lang -> lang
  in
  let tag_name = "checkentail" in
  let font_name = "Monospace 11" in

  object (self)
    val delegate = GSourceView2.source_view ()
    
    initializer
      delegate#set_show_line_numbers true;
      delegate#set_auto_indent true;
      delegate#set_tab_width 2;
      delegate#set_insert_spaces_instead_of_tabs true;
      delegate#misc#modify_font_by_name font_name;
      delegate#set_show_line_marks true;
      let buffer = delegate#source_buffer in
      buffer#set_language (Some (get_sleek_lang ()));
      buffer#set_text text;
      buffer#set_highlight_syntax true;
      ignore (buffer#create_tag ~name:tag_name [`BACKGROUND "light gray"])

    method coerce = delegate#coerce
    method source_buffer = delegate#source_buffer

    (* highlight checkentail command
     * by applying checkentail tag on that part of source code *)
    method hl_entailment (e: entailment): unit =
      self#clear_highlight ();
      let start = self#source_buffer#get_iter_at_char e.start_char in
      let stop = self#source_buffer#get_iter_at_char e.stop_char in
      self#source_buffer#apply_tag_by_name tag_name start stop

    (* highlight all checkentail commands *)
    method hl_all_entailement () : unit =
      let hl (e: entailment) : unit =
        let start = self#source_buffer#get_iter_at_char e.start_char in
        let stop = self#source_buffer#get_iter_at_char e.stop_char in
        self#source_buffer#apply_tag_by_name tag_name start stop
      in
      let src = self#source_buffer#get_text () in
      let e_list = SourceUtils.parse_entailment_list src in
      List.iter hl e_list

    (* clear current highlight
     * by removing checkentail tag in current source code *)
    method clear_highlight () =
      let start = self#source_buffer#get_iter `START in
      let stop = self#source_buffer#get_iter `END in
      self#source_buffer#remove_tag_by_name tag_name start stop

  end

(***************
 * Main window
 * *************)
let create_yes_no_cancel_dialog
    ?msg:(msg="Yes or No?")
    ?yes_label:(yes_label="Yes")
    ?no_label:(no_label="No")
    () =
  let dialog = GWindow.dialog () in
  let hbox = GPack.hbox 
    ~spacing:10 ~border_width:5
    () in
  let icon = GMisc.image 
    ~stock:`DIALOG_WARNING 
    ~icon_size:`DIALOG
    () in
  let label = GMisc.label
    ~text:msg
    ~justify:`LEFT
    () in
  hbox#add icon#coerce;
  hbox#add label#coerce;
  dialog#vbox#add hbox#coerce;
  dialog#add_button yes_label `YES;
  dialog#add_button no_label `NO;
  dialog#add_button_stock `CANCEL `CANCEL;
  dialog

let create_statusbar () =
  let statusbar = GMisc.statusbar () in
  let context = statusbar#new_context ~name:"statusbar" in
  let _ = context#push "" in
  statusbar

let create_residue_view () =
  let view = GText.view
    ~editable:false
    () in
  view

(* wrap child in a scrolled window and return that window *)
let create_scrolled_win child = 
  let scroll_win = GBin.scrolled_window 
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC 
    () in
  scroll_win#add child#coerce;
  scroll_win

let ui_info =
  "<ui>\
  <menubar name='MenuBar'>\
    <menu action='FileMenu'>\
      <menuitem action='New'/>\
      <menuitem action='Open'/>\
      <menuitem action='Save'/>\
      <separator/>\
      <menuitem action='Quit'/>\
    </menu>\
    <menu action='PreferencesMenu'>\
      <menu action='TheoremProverMenu'>\
        <menuitem action='Omega'/>\
        <menuitem action='Mona'/>\
        <menuitem action='Redlog'/>\
      </menu>\
      <menuitem action='EPS'/>\
      <menuitem action='EAP'/>\
    </menu>\
    <menu action='HelpMenu'>\
      <menuitem action='About'/>\
    </menu>\
  </menubar>\
  <toolbar name='ToolBar'>\
    <toolitem action='New'/>\
    <toolitem action='Open'/>\
    <toolitem action='Save'/>\
    <separator/>\
    <toolitem action='Execute'/>\
  </toolbar>\
</ui>"

class mainwindow =
  let win = GWindow.window
    ~height:600 ~width:900
    ~title:"New file - Sleek" 
    ~allow_shrink:true
    () in
  object (self)
    inherit GWindow.window win#as_window as super

    (* gui components *)
    val source_view = new sleek_source_view ()
    val entailment_list = new entailment_list ()
    (*val statusbar = create_statusbar ()*)
    val residue_view = create_residue_view ()
    (* data *)
    val mutable current_file = None
      
    initializer
      (* initialize components *)
      let residue_panel =
        let label = GMisc.label 
          ~text:"Residue:" 
          ~xalign:0.0 ~yalign:0.0
          ~xpad:5 ~ypad:5
          () in
        let residue_scrolled = create_scrolled_win residue_view in
        let vbox = GPack.vbox () in
        vbox#pack ~expand:false label#coerce;
        vbox#pack ~expand:true residue_scrolled#coerce;
        vbox
      in
      let entail_panel =
        let list_scrolled = create_scrolled_win entailment_list in
        let hpaned = GPack.paned `HORIZONTAL () in
        hpaned#set_position 500; (* FIXME *)
        hpaned#pack1 list_scrolled#coerce;
        hpaned#pack2 ~resize:true ~shrink:true residue_panel#coerce;
        hpaned
      in
      let main_panel =
        let vpaned = GPack.paned `VERTICAL () in
        vpaned#set_position 380; (* FIXME *)
        let source_scrolled = create_scrolled_win source_view in
        vpaned#pack1 ~resize:true ~shrink:true source_scrolled#coerce;
        vpaned#pack2 entail_panel#coerce;
        vpaned
      in
      (* arrange components on main window *)
      let ui = self#setup_ui_manager () in
      let toolbar = ui#get_widget "/ToolBar" in
      let menubar = ui#get_widget "/MenuBar" in
      let vbox = GPack.vbox ~packing:self#add () in
      vbox#pack menubar;
      vbox#pack toolbar;
      vbox#pack ~expand:true ~fill:true main_panel#coerce;
      (*vbox#pack ~expand:false statusbar#coerce;*)

      (* set event handlers *)
      ignore (self#event#connect#delete ~callback:(fun _ -> self#quit ()));
      ignore (source_view#source_buffer#connect#modified_changed
        ~callback:self#source_changed_handler);
      ignore (entailment_list#selection#connect#changed
        ~callback:self#entailment_list_selection_changed_handler);
      entailment_list#set_checkall_handler self#run_all_handler;


    (* Setup UIManager for creating Menubar and Toolbar *)
    method setup_ui_manager () =
      let a = GAction.add_action in
      let radio = GAction.group_radio_actions in
      let ra = GAction.add_radio_action in
      let ta = GAction.add_toggle_action in
      let actions = GAction.action_group ~name:"Actions" () in
      GAction.add_actions actions [ 
        a "FileMenu" ~label:"_File";
        a "PreferencesMenu" ~label:"_Preferences";
        a "TheoremProverMenu" ~label:"_Prover";
        a "HelpMenu" ~label:"_Help";
        a "New" ~stock:`NEW ~tooltip:"Create a new file"
          ~callback:(fun _ -> ignore (self#newfile_handler ()));
        a "Open" ~stock:`OPEN ~tooltip:"Open a file"
          ~callback:(fun _ -> ignore (self#open_handler ()));
        a "Save" ~stock:`SAVE ~tooltip:"Save current file"
          ~callback:(fun _ -> ignore (self#save_handler ()));
        a "Quit" ~stock:`QUIT ~tooltip:"Quit"
          ~callback:(fun _ -> ignore (self#quit ()));
        a "About" ~label:"_About" ~tooltip:"About HIP/Sleek";
        a "Execute" ~stock:`EXECUTE ~tooltip:"Check all entailments"
          ~callback:(fun _ -> self#run_all_handler ());
        ta "EPS" ~label:"Predicate Specialization"
          ~callback:(fun _ -> print_endline "eps");
        ta "EAP" ~label:"Aggressive Prunning"
          ~callback:(fun _ -> print_endline "eap");
        radio ~init_value:0 [
          ra "Omega" 0 ~label:"_Omega";
          ra "Mona" 1 ~label:"_Mona";
          ra "Redlog" 2 ~label:"_Redlog";
        ];
      ];
      let ui = GAction.ui_manager () in
      ui#insert_action_group actions 0;
      self#add_accel_group ui#get_accel_group;
      ui#add_ui_from_string ui_info;
      ui
      

    (* open file chooser dialog with parent window
     * return choosen file name 
     *)
    method show_file_chooser ?title:(title="Slect file") action : string option =
      let all_files () =
        GFile.filter ~name:"All files" ~patterns:["*"] ()
      in
      let slk_files () =
        GFile.filter ~name:"Sleek files" ~patterns:["*.slk"] ()
      in
      let dialog = GWindow.file_chooser_dialog
        ~action ~title
        ~parent:self 
        () in
      let dir = match current_file with
        | Some name -> Filename.dirname name
        | None -> Filename.current_dir_name
      in
      ignore (dialog#set_current_folder dir);
      dialog#add_button_stock `CANCEL `CANCEL;
      dialog#add_select_button_stock `OPEN `OPEN;
      dialog#add_filter (slk_files ());
      dialog#add_filter (all_files ());
      let res = match dialog#run () with
        | `OPEN -> dialog#filename
        | `DELETE_EVENT | `CANCEL -> None 
      in
      dialog#destroy ();
      res

    (* open an yes/no/cancel dialog which asks user for
     * saving of modified document *)
    method ask_for_saving () =
      let fname = Filename.basename (self#string_of_current_file ()) in
      let save_msg = match current_file with
        | Some _ -> "Save"
        | None -> "Save as..."
      in
      let dialog = create_yes_no_cancel_dialog
        ~msg:("\nSave changes to file \"" ^ fname ^ "\"\nbefore closing?\n")
        ~yes_label:save_msg
        ~no_label:"Discard"
        () in
      let response = dialog#run () in
      let res = match response with
        | `YES -> self#save_handler ()
        | `NO -> true
        | `CANCEL | _ -> false
      in dialog#destroy ();
      res

    method replace_source (new_src: string): unit =
      source_view#source_buffer#begin_not_undoable_action ();
      source_view#source_buffer#set_text new_src;
      source_view#source_buffer#set_modified false;
      source_view#source_buffer#end_not_undoable_action ();
      entailment_list#update_source new_src;
      residue_view#buffer#set_text ""
      

    method private string_of_current_file () =
      match current_file with
      | Some fname -> fname
      | None -> "New file"

    method file_closing_check (): bool =
      if source_view#source_buffer#modified then
        self#ask_for_saving ()
      else
        true

    method open_file (fname: string): unit =
      current_file <- (Some fname);
      self#replace_source (FileUtils.read_from_file fname);
      self#update_win_title ()

    method update_win_title () =
      let fname = self#string_of_current_file () in
      let title = 
        if source_view#source_buffer#modified then
          fname ^ "* - Sleek"
        else
          fname ^ " - Sleek"
      in
      self#set_title title;
        
    method get_text () = source_view#source_buffer#get_text ()


    (*********************
     * Actions handlers 
     *********************)

    method private newfile_handler () =
      if self#file_closing_check () then begin
        current_file <- None;
        self#replace_source ""
      end

    (* Toolbar's Open button clicked *)
    method private open_handler () : bool =
      if self#file_closing_check () then
        let fname = self#show_file_chooser `OPEN in
        match fname with
        | None -> false
        | Some fname -> (self#open_file fname; true)
      else
        true

    (* Toolbar's Save button clicked 
     * return true if file is saved successfully
     * return false if user don't select a file to save *)
    method private save_handler () : bool =
      let text = source_view#source_buffer#get_text () in
      match current_file with
      | Some name ->
          FileUtils.write_to_file name text;
          source_view#source_buffer#set_modified false;
          self#update_win_title ();
          true
      | None ->
          let fname = self#show_file_chooser `SAVE in
          match fname with
          | None -> false
          | Some fname -> FileUtils.write_to_file fname text; true

    (* Toolbar's Run all button clicked or Validity column header clicked *)
    method private run_all_handler () =
      let src = self#get_text () in
      entailment_list#check_all (fun e -> fst (SleekHelper.checkentail src e));
      source_view#hl_all_entailement ()

    (* Source buffer modified *)
    method private source_changed_handler () =
      entailment_list#update_source (self#get_text ());
      self#update_win_title ()

    method private entailment_list_selection_changed_handler () =
      let entail = entailment_list#get_selected_entailment () in
      match entail with
      | None -> ()
      | Some e -> begin
        let src = self#get_text () in
        let valid, residue = SleekHelper.checkentail src e in
        entailment_list#set_selected_entailment_validity valid;
        residue_view#buffer#set_text residue;
        source_view#hl_entailment e
      end

    method private quit () =
      if self#file_closing_check () then
        let _ = GMain.quit () in
        false
      else
        true

  end


(**********************
 * MAIN FUNCTION
 **********************)
let get_fname () : string option =
  let len = Array.length Sys.argv in
  if len = 1 then
    None
  else
    Some (Array.get Sys.argv 1)

let init win =
  let fname = get_fname () in
  match fname with
  | Some name -> win#open_file name
  | None ->
      let ex = "./examples/sleek.slk" in
      if Sys.file_exists ex then win#open_file ex

let _ =
  let win = new mainwindow in
  win#show ();
  init win;
  GMain.Main.main ()
