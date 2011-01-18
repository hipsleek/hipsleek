(*************************
 * GUI frontend for Sleek
 *************************)

open GEntailmentList
open GSleekSourceView

module SU = GUtil.SourceUtil
module FU = GUtil.FileUtil
module SH = GUtil.SleekHelper
module TP = Tpdispatcher

let create_residue_view () =
  let view = GText.view
    ~editable:false
    ~wrap_mode:`WORD
    () in
  view

(* wrap child in a scrolled window and return that window *)
class mainwindow () =
  let ui_info =
    "<ui>\
    <menubar name='MenuBar'>\
      <menu action='FileMenu'>\
        <menuitem action='New'/>\
        <menuitem action='Open'/>\
        <menuitem action='Save'/>\
        <separator/>\
        <menuitem action='Quit'/>\
      </menu>\n
      <menu action='PreferencesMenu'>\
        <menu action='TheoremProverMenu'>\
          <menuitem action='Omega'/>\
          <menuitem action='Mona'/>\
          <menuitem action='Cvc3'/>\
          <menuitem action='Redlog'/>\
          <menuitem action='OM'/>\
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
  in
  let win = GWindow.window
    ~height:750 ~width:1000
    ~title:"New file - Sleek" 
    ~allow_shrink:true
    () in
  object (self)
    inherit GWindow.window win#as_window as super

    (* gui components *)
    val source_view = new sleek_source_view ()
    val entailment_list = new entailment_list ()
    val residue_view = create_residue_view ()
    (* data *)
    val mutable current_file = None
    val mutable debug_log_window = None
    val mutable prover_log_window = None
      
    initializer
      (* initialize components *)
      let residue_panel =
        let label = GMisc.label 
          ~text:"Residue and Contexts:" 
          ~xalign:0.0 ~yalign:0.0
          ~xpad:5 ~ypad:5
          () in
        let residue_scrolled = GUtil.create_scrolled_win residue_view in
        let vbox = GPack.vbox () in
        vbox#pack ~expand:false label#coerce;
        vbox#pack ~expand:true residue_scrolled#coerce;
        vbox
      in
      let entail_panel =
        let list_scrolled = GUtil.create_scrolled_win entailment_list in
        let buttons = GPack.button_box 
          `HORIZONTAL ~layout:`START
          ~border_width:10
          () in
        let check_btn = GButton.button
          ~label:"Check Entailment"
          ~packing:buttons#add
          () in
        ignore (check_btn#connect#clicked ~callback:self#check_selected_entailment);
        let show_debug_log_btn = GButton.button
          ~label:"Show Debug Log"
          ~packing:buttons#add
          () in
        ignore (show_debug_log_btn#connect#clicked ~callback:self#show_debug_log);
        let show_prover_log_btn = GButton.button
          ~label:"Show Prover Log"
          ~packing:buttons#add
          () in
        ignore (show_prover_log_btn#connect#clicked ~callback:self#show_prover_log);
        let vbox = GPack.vbox () in
        vbox#pack ~expand:true list_scrolled#coerce;
        vbox#pack ~expand:false buttons#coerce;
        let hpaned = GPack.paned `HORIZONTAL () in
        hpaned#set_position 580;
        hpaned#pack1 vbox#coerce;
        hpaned#pack2 ~resize:true ~shrink:true residue_panel#coerce;
        hpaned
      in
      let main_panel =
        let vpaned = GPack.paned `VERTICAL () in
        vpaned#set_position 450;
        let source_scrolled = GUtil.create_scrolled_win source_view in
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

      (* set event handlers *)
      ignore (self#event#connect#delete ~callback:(fun _ -> self#quit ()));
      ignore (source_view#source_buffer#connect#modified_changed
        ~callback:self#source_changed_handler);
      ignore (entailment_list#selection#connect#changed
        ~callback:self#check_selected_entailment);
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
        a "About" ~label:"_About" ~tooltip:"About HIP/Sleek"
          ~callback:(fun _ -> ignore (self#show_about_dialog ()));
        a "Execute" ~stock:`EXECUTE ~tooltip:"Check all entailments"
          ~callback:(fun _ -> self#run_all_handler ());
        ta "EPS" ~label:"Enable Predicate Specialization"
          ~callback:(fun act -> Globals.allow_pred_spec := act#get_active);
        ta "EAP" ~label:"Enable Aggressive Prunning"
          ~callback:(fun act -> Globals.enable_aggressive_prune := act#get_active);
        radio ~init_value:0 ~callback:self#set_theorem_prover [
          ra "Omega" 0 ~label:"_Omega";
          ra "Mona" 1 ~label:"_Mona";
          ra "Cvc3" 2 ~label:"_Cvc3";
          ra "Redlog" 3 ~label:"_Redlog";
          ra "OM" 4 ~label:"Omega _And Mona";
        ];
      ];
      let ui = GAction.ui_manager () in
      ui#insert_action_group actions 0;
      self#add_accel_group ui#get_accel_group;
      ignore (ui#add_ui_from_string ui_info);
      ui
      

    (* open file chooser dialog with parent window
     * return choosen file name 
     *)
    method show_file_chooser ?(title="Select file") action : string option =
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
      let icon = GMisc.image 
        ~stock:`DIALOG_WARNING 
        ~icon_size:`DIALOG
        () in
      let response = GToolbox.question_box
        ~title:(fname ^ " is modified")
        ~buttons:["Discard"; "Cancel"; save_msg]
        ~icon:icon#coerce
        ~default:3
        ("\nSave changes to file \"" ^ fname ^ "\"\nbefore closing?\n")
        in
      let res = match response with
        | 1 -> true
        | 3 -> self#save_handler ()
        | _ -> false
      in res

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
      self#replace_source (FU.read_from_file fname);
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

    method set_theorem_prover id =
      let provers = [TP.OmegaCalc; TP.Mona; TP.Cvc3; TP.Redlog; TP.OM] in
      let tp = List.nth provers id in
      TP.change_prover tp;
      let tp_name = TP.string_of_tp tp in
      GUtil.log (Printf.sprintf "Use %s as backend prover." tp_name)

    method check_selected_entailment () =
      let entail = entailment_list#get_selected_entailment () in
      match entail with
      | None -> ()
      | Some e -> begin
          let src = self#get_text () in
          let valid, residue = SH.checkentail src e in
          entailment_list#set_selected_entailment_validity valid;
          residue_view#buffer#set_text residue;
          source_view#hl_entailment e
        end

    method show_debug_log () =
      let log = Debug.get_debug_log () in
      let win = match debug_log_window with
        | Some win-> 
            win#set_log log;
            win
        | None ->
            let win = new GLogViewWindow.log_view_window
              ~title:"Development Debug Log" log () in
            debug_log_window <- Some win;
            win
      in
      win#present ()

    method show_prover_log () =
      let log = TP.get_prover_log () in
      let title = (TP.get_current_tp_name ()) ^ " Log" in
      let win = new GLogViewWindow.log_view_window ~title log () in
      win#present ()

    method show_about_dialog () =
        let dialog = GWindow.about_dialog 
          ~name:"HIP/Sleek"
          ~authors:["Wei Ngan Chin"; "Huu Hai Nguyen"; "Cristina David"; "Cristian Gherghina"]
          ~version:"1.0"
          ~website:"http://loris-7.ddns.comp.nus.edu.sg/~project/hip/index.html"
          ~parent:self
          () in
        ignore (dialog#connect#response ~callback:(fun _ -> dialog#destroy ()));
        dialog#show ()

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
        let fname = self#show_file_chooser ~title:"Open File" `OPEN in
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
          FU.write_to_file name text;
          source_view#source_buffer#set_modified false;
          self#update_win_title ();
          true
      | None ->
          let fname = self#show_file_chooser ~title:"Save As..." `SAVE in
          match fname with
          | None -> false
          | Some fname -> FU.write_to_file fname text; true

    (* Toolbar's Run all button clicked or Validity column header clicked *)
    method private run_all_handler () =
      let src = self#get_text () in
      entailment_list#check_all (fun e -> fst (SH.checkentail src e));
      source_view#hl_all_entailement ()

    (* Source buffer modified *)
    method private source_changed_handler () =
      entailment_list#update_source (self#get_text ());
      source_view#clear_highlight ();
      self#update_win_title ()

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
let initialize () =
  ignore (GtkMain.Main.init ());
  Debug.devel_debug_on := true;
  Debug.log_devel_debug := true;
  TP.enable_log_for_all_provers ();
  TP.start_prover ()

let finalize () =
  TP.stop_prover ()

let usage_msg = Sys.argv.(0) ^ " [options] <source file>"
let arguments = [
  ("-v", Arg.Set GUtil.verbose_flag, "Verbose")
  ]

let _ =
  initialize ();
  let win = new mainwindow () in
  Arg.parse arguments win#open_file usage_msg;
  win#show ();
  GMain.Main.main ();
  finalize ()

