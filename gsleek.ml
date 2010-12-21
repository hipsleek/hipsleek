(*************************
 * GUI frontend for Sleek
 *************************)

open GMain
open Printf

(* configurations *)
let win_width = 1000 (* default main window width *)
let win_height = 700 (* default main window height *)

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

  (* write text to a file with name fname *)
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
    formula: string;
    start_char: int;
    start_line: int;
    stop_char: int;
    stop_line: int;
  }

  let checkentail_re = Str.regexp "checkentail \\([^\\.]+\\)\\."
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

end (* SourceUtils *)

open SourceUtils


(*********************************
 * Entailment list model
 *********************************)
let cols = new GTree.column_list
let col_id = cols#add Gobject.Data.int
let col_line = cols#add Gobject.Data.int
let col_formula = cols#add Gobject.Data.string

class entailment_list_model ?source:(src = "") () =
  object (self)
    val delegate = GTree.list_store cols
    val mutable entailment_list = []
    val mutable count = 0

    initializer
      self#update_source src
    
    method coerce = delegate#coerce

    method append_one_entailment (e: entailment) =
      let iter = delegate#append () in
      delegate#set ~row:iter ~column:col_id count;
      delegate#set ~row:iter ~column:col_line e.start_line;
      delegate#set ~row:iter ~column:col_formula e.formula;
      count <- count + 1

    method update_source (source: string) =
      delegate#clear ();
      count <- 0;
      entailment_list <- parse_entailment_list source;
      List.iter self#append_one_entailment entailment_list

    method get_entailment_of_tree_path path =
      let row = delegate#get_iter path in
      let id = delegate#get ~row ~column:col_id in
      List.nth entailment_list id

  end


(*********************************
 * Entailment list view
 *********************************)
class entailment_list_view ?model:(model = new entailment_list_model ()) () =
  object (self)
    val delegate = GTree.view ()
    val mutable model = model

    initializer
      delegate#selection#set_mode `SINGLE;
      let col = GTree.view_column
        ~title:"Line"
        ~renderer:(GTree.cell_renderer_text [], ["text", col_line])
        () in
      ignore (delegate#append_column col);
      let col = GTree.view_column
        ~title:"Entailment"
        ~renderer:(GTree.cell_renderer_text [], ["text", col_formula])
        () in
      ignore (delegate#append_column col);
      delegate#set_model (Some model#coerce)

    method coerce = delegate#coerce
    method selection = delegate#selection

    method set_model new_model =
      model <- new_model;
      delegate#set_model (Some model#coerce)

    method get_selected_entailment () =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [] -> None
      | h::t -> Some (model#get_entailment_of_tree_path h)

  end


(***********************
 * Sleek source editor
 ***********************)
class sleek_source_view ?text:(text = "") () =

  let get_sleek_lang () =
    let lang_mime_type = "text/x-sleek" in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    match language_manager#guess_language ~content_type:lang_mime_type () with
    | None -> failwith (sprintf "no language for %s" lang_mime_type)
    | Some lang -> lang
  in

  object (self)
    val tag_name = "checkentail"
    val font_name = "Monospace 11"
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

let create_statusbar () =
  let statusbar = GMisc.statusbar () in
  let context = statusbar#new_context ~name:"statusbar" in
  let _ = context#push "" in
  statusbar

let create_toolbar () =
  let toolbar = GButton.toolbar 
    ~orientation:`HORIZONTAL
    ~style:`ICONS
    (*~height:50*)
    () in
  toolbar#set_icon_size `LARGE_TOOLBAR;
  toolbar

(* wrap child in a scrolled window and return that window *)
let create_scrolled_win child () = 
  let scroll_win = GBin.scrolled_window 
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC 
    () in
  scroll_win#add child#coerce;
  scroll_win

class mainwindow =
  let win = GWindow.window
    ~height:win_height ~width:win_width
    ~title:"New file - Sleek" 
    ~allow_shrink:true
    () in
  object (self)
    inherit GWindow.window win#as_window as super

    (* gui components *)
    val toolbar = create_toolbar ()
    val open_btn = GButton.tool_button ~stock:`OPEN ~homogeneous:true ()
    val save_btn = GButton.tool_button ~stock:`SAVE ~homogeneous:true ()
    val exec_btn = GButton.tool_button ~stock:`EXECUTE ~homogeneous:true ()
    val run_one_btn = GButton.button ~label:"Run selected" ()
    val run_all_btn = GButton.button ~label:"Run all" ()
    val source_view = new sleek_source_view ()
    val entailment_list = new entailment_list_view ()
    val statusbar = create_statusbar ()
    (* data *)
    val mutable current_filename = ""
    val mutable source_is_changed = false
    val model = new entailment_list_model ()
      
    initializer
      (* initialize components *)
      entailment_list#set_model model;
      toolbar#insert open_btn;
      toolbar#insert save_btn;
      (*toolbar#insert (GButton.separator_tool_item ());*)
      (*toolbar#insert exec_btn;*)

      (* arrange components on main window *)
      let vbox = GPack.vbox ~packing:self#add () in
      vbox#pack ~expand:false toolbar#coerce;
      let vpaned = GPack.paned `VERTICAL () in
      (* default position is about 2/3 of window's height *)
      vpaned#set_position (win_height*7/12);
      vbox#pack ~expand:true ~fill:true vpaned#coerce;
      let source_scrolled = create_scrolled_win source_view () in
      vpaned#pack1 ~resize:true ~shrink:true source_scrolled#coerce;
      let list_scrolled = create_scrolled_win entailment_list () in
      vpaned#pack2 list_scrolled#coerce;
      let bbox = GPack.button_box
        `HORIZONTAL ~layout:`END
        ~border_width:5 ~spacing:5
        ~child_height:35
        () in
      bbox#pack run_one_btn#coerce;
      bbox#pack run_all_btn#coerce;
      vbox#pack ~expand:false bbox#coerce;
      vbox#pack ~expand:false statusbar#coerce;

      (* set event handlers *)
      ignore (self#connect#destroy (fun _ -> quit ()));
      ignore (open_btn#connect#clicked ~callback:self#open_handler);
      ignore (save_btn#connect#clicked ~callback:self#save_handler);
      ignore (source_view#source_buffer#connect#changed
        ~callback:self#source_changed_handler);
      ignore (entailment_list#selection#connect#changed
        ~callback:self#entailment_list_selection_changed_handler)


    (* open file chooser dialog with parent window
     * return choosen file name 
     *)
    method show_file_chooser () : string option =
      let all_files () =
        GFile.filter ~name:"All files" ~patterns:["*"] ()
      in
      let slk_files () =
        GFile.filter ~name:"Sleek files" ~patterns:["*.slk"] ()
      in
      let dialog = GWindow.file_chooser_dialog
        ~action:`OPEN
        ~title:"Open Sleek file"
        ~parent:self () in
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

    method replace_source (new_src: string): unit =
      source_view#source_buffer#set_text new_src;
      source_is_changed <- false;
      model#update_source new_src;

    method get_text () = source_view#source_buffer#get_text ()

    (*********************
     * Actions handlers 
     *********************)
    method private open_handler () =
      let fname = self#show_file_chooser () in
      match fname with
      | None -> ()
      | Some fname -> begin
          current_filename <- fname;
          self#set_title (fname ^ " - Sleek");
          let src = FileUtils.read_from_file fname in
          self#replace_source src
        end

    method private save_handler () =
      let text = source_view#source_buffer#get_text () in
      FileUtils.write_to_file current_filename text

    method private source_changed_handler () =
      source_is_changed <- true;
      self#set_title (current_filename ^ "* - Sleek");
      model#update_source (self#get_text ())

    method private entailment_list_selection_changed_handler () =
      let entail = entailment_list#get_selected_entailment () in
      match entail with
      | None -> ()
      | Some e -> source_view#hl_entailment e

  end


(**********************
 * MAIN FUNCTION
 **********************)
let _ =
  let win = new mainwindow in
  win#show ();
  Main.main ()
